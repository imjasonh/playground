//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! Thin glue: D1 for posts/subscribers/credentials, R2 for images, signed
//! cookies for admin auth. HTML and WebAuthn live in the host-tested modules.

use serde::Deserialize;
use worker::d1::{D1Database, D1Type};
use worker::wasm_bindgen::JsValue;
use worker::{event, Bucket, Context, Env, FormEntry, Headers, Method, Request, Response, Result};

use crate::auth::{
    challenge_cookie_header, clear_cookie_header, make_challenge_cookie, make_session_cookie,
    session_cookie_header, verify_challenge_cookie, verify_password, verify_session_cookie,
    CHALLENGE_COOKIE, SESSION_COOKIE,
};
use crate::html::{
    admin_compose, edit_page, grouped_has_images, image_ext_for, index_view, is_allowed_image_type,
    is_valid_email, login_page, passkeys_page, post_view, rss_feed, subscribe_form,
    subscribe_thanks, validate_post_body, Post, PostImage, PAPERCLIP_KEY,
};
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
}

impl Site {
    fn from_env(env: &Env) -> Result<Self> {
        Ok(Self {
            title: env
                .var("SITE_TITLE")
                .map(|v| v.to_string())
                .unwrap_or_else(|_| "y".into()),
            url: env
                .var("SITE_URL")
                .map(|v| v.to_string())
                .unwrap_or_else(|_| "https://y.imjasonh.workers.dev".into()),
            session_secret: env
                .secret("SESSION_SECRET")
                .map(|v| v.to_string())
                .unwrap_or_default(),
            password_hash: env
                .secret("ADMIN_PASSWORD_HASH")
                .map(|v| v.to_string())
                .unwrap_or_default(),
        })
    }

    fn rp(&self) -> std::result::Result<RpContext, String> {
        RpContext::from_site(&self.url, &self.title)
    }
}

#[event(fetch)]
async fn fetch(req: Request, env: Env, ctx: Context) -> Result<Response> {
    match handle_fetch(req, env, ctx).await {
        Ok(resp) => Ok(resp),
        Err(e) => {
            worker::console_error!("{}", e);
            text(500, "internal error")
        }
    }
}

async fn handle_fetch(mut req: Request, env: Env, _ctx: Context) -> Result<Response> {
    let method = req.method();
    let url = req.url()?;
    let path = url.path().to_string();
    let site = Site::from_env(&env)?;
    let db = env.d1("DB")?;
    let images = env.bucket("IMAGES")?;
    let now = (js_now()) as u64;

    let Some(route) = route::parse(method.as_ref(), &path) else {
        return text(404, "not found");
    };

    match route {
        Route::Home => handle_home(&req, &db, &site, now).await,
        Route::Post { id } => handle_post(&req, &db, &site, now, id).await,
        Route::Feed => handle_feed(&db, &site, now).await,
        Route::Image { key } => handle_image(&images, &key).await,
        Route::Subscribe if method == Method::Get => Ok(html(200, subscribe_form(&site.title))?),
        Route::Subscribe => handle_subscribe_post(&mut req, &db, &site, now).await,
        Route::AdminLogin if method == Method::Get => handle_login_get(&req, &db, &site, now).await,
        Route::AdminLogin => handle_login_post(&mut req, &db, &site, now).await,
        Route::LoginPasskeyOptions => handle_login_passkey_options(&db, &site, now).await,
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
            handle_register_options(&db, &site, now).await
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
            delete_credential(&db, id).await?;
            redirect("/admin/passkeys")
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

async fn handle_home(req: &Request, db: &D1Database, site: &Site, now: u64) -> Result<Response> {
    let before = query(req, "before").and_then(|s| s.parse::<i64>().ok());
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
    if let Some(obj) = bucket.get(key).execute().await? {
        let headers = Headers::new();
        if let Some(ct) = obj.http_metadata().content_type {
            headers.set("Content-Type", &ct)?;
        }
        headers.set("etag", &obj.http_etag())?;
        headers.set("Cache-Control", "public, max-age=31536000, immutable")?;
        let bytes = match obj.body() {
            Some(b) => b.bytes().await?,
            None => return text(404, "not found"),
        };
        return Ok(Response::from_bytes(bytes)?.with_headers(headers));
    }
    // CSS references /img/assets/paperclip.png; serve the committed asset if
    // it was never uploaded to R2 (the TS Worker 404'd and broke the clip).
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
    let form = req.form_data().await?;
    let email = form
        .get_field("email")
        .unwrap_or_default()
        .trim()
        .to_lowercase();
    if !is_valid_email(&email) {
        return text(400, "invalid email");
    }
    if !subscriber_exists(db, &email).await? {
        insert_interested(db, &email, now as i64).await?;
    }
    html(200, subscribe_thanks(&site.title))
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
    let form = req.form_data().await?;
    let password = form.get_field("password").unwrap_or_default();
    if !verify_password(&password, &site.password_hash) {
        return redirect("/admin/login?err=1");
    }
    let value = make_session_cookie(&site.session_secret, now);
    let resp = redirect("/admin/passkeys?bootstrap=1")?;
    set_cookie(resp.headers(), &session_cookie_header(&value))?;
    Ok(resp)
}

async fn handle_login_passkey_options(db: &D1Database, site: &Site, now: u64) -> Result<Response> {
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

async fn handle_login_passkey_verify(
    req: &mut Request,
    db: &D1Database,
    site: &Site,
    now: u64,
) -> Result<Response> {
    let expected = verify_challenge_cookie(
        &site.session_secret,
        cookie(req, CHALLENGE_COOKIE).as_deref(),
        now,
    );
    let Some(expected) = expected else {
        return with_cleared_challenge(text(400, "challenge expired")?);
    };
    let body = req.text().await.unwrap_or_default();
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
            update_counter(db, &stored.id, info.new_counter).await?;
            let value = make_session_cookie(&site.session_secret, now);
            let resp = json(200, r#"{"ok":true}"#)?;
            set_cookie(resp.headers(), &session_cookie_header(&value))?;
            with_cleared_challenge(resp)
        }
        Err(e) => with_cleared_challenge(text(400, &e)?),
    }
}

async fn handle_admin_get(req: &Request, db: &D1Database, site: &Site) -> Result<Response> {
    let reply_to = match query(req, "reply_to").and_then(|s| s.parse::<i64>().ok()) {
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

async fn handle_register_options(db: &D1Database, site: &Site, now: u64) -> Result<Response> {
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
    let expected = verify_challenge_cookie(
        &site.session_secret,
        cookie(req, CHALLENGE_COOKIE).as_deref(),
        now,
    );
    let Some(expected) = expected else {
        return with_cleared_challenge(text(400, "challenge expired")?);
    };
    let body = req.text().await.unwrap_or_default();
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
            insert_credential(
                db,
                &info.credential_id,
                &info.public_key,
                info.counter,
                info.transports.as_ref().map(|t| t.join(",")),
                &label,
                now as i64,
            )
            .await?;
            with_cleared_challenge(json(200, r#"{"ok":true}"#)?)
        }
        Err(e) => with_cleared_challenge(text(400, &e)?),
    }
}

async fn handle_create_post(
    req: &mut Request,
    db: &D1Database,
    bucket: &Bucket,
    now: u64,
) -> Result<Response> {
    let form = req.form_data().await?;
    let body = form
        .get_field("body")
        .unwrap_or_default()
        .trim()
        .to_string();
    let mut files: Vec<(String, Vec<u8>)> = Vec::new();
    if let Some(entries) = form.get_all("image") {
        for entry in entries {
            if let FormEntry::File(f) = entry {
                if f.size() == 0 {
                    continue;
                }
                let ty = f.type_();
                if !is_allowed_image_type(&ty) {
                    return text(400, &format!("unsupported image type: {ty}"));
                }
                files.push((ty, f.bytes().await?));
            }
        }
    }
    if let Err(msg) = validate_post_body(&body, !files.is_empty()) {
        return text(400, &msg);
    }
    let parent_id = match form.get_field("parent_id") {
        Some(s) if !s.is_empty() => {
            let Ok(n) = s.parse::<i64>() else {
                return text(400, "bad parent_id");
            };
            if get_post(db, n).await?.is_none() {
                return text(400, "parent post not found");
            }
            Some(n)
        }
        _ => None,
    };
    let post_id = insert_post(db, &body, now as i64, parent_id).await?;
    for (i, (ty, bytes)) in files.iter().enumerate() {
        let ext = image_ext_for(ty).unwrap_or("bin");
        let key = format!("{post_id}/{i}.{ext}");
        bucket
            .put(&key, bytes.clone())
            .http_metadata(worker::HttpMetadata {
                content_type: Some(ty.clone()),
                ..Default::default()
            })
            .execute()
            .await?;
        insert_post_image(db, post_id, &key, ty, i as i64).await?;
    }
    redirect(&format!("/admin?reply_to={post_id}"))
}

async fn handle_delete_post(db: &D1Database, bucket: &Bucket, id: i64) -> Result<Response> {
    let imgs = delete_post(db, id).await?;
    for key in imgs {
        let _ = bucket.delete(key).await;
    }
    redirect("/admin")
}

async fn handle_edit_get(db: &D1Database, site: &Site, id: i64) -> Result<Response> {
    let Some(post) = get_post(db, id).await? else {
        return text(404, "not found");
    };
    html(200, edit_page(&site.title, &post))
}

async fn handle_edit_post(req: &mut Request, db: &D1Database, id: i64) -> Result<Response> {
    let form = req.form_data().await?;
    let body = form
        .get_field("body")
        .unwrap_or_default()
        .trim()
        .to_string();
    let grouped = images_for_posts(db, &[id]).await?;
    if let Err(msg) = validate_post_body(&body, grouped_has_images(&grouped, id)) {
        return text(400, &msg);
    }
    update_post_body(db, id, &body).await?;
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
) -> Result<i64> {
    let parent = match parent_id {
        Some(id) => JsValue::from_f64(id as f64),
        None => JsValue::NULL,
    };
    let result = db
        .prepare("INSERT INTO posts (body, created_at, parent_id) VALUES (?1, ?2, ?3)")
        .bind(&[
            JsValue::from_str(body),
            JsValue::from_f64(created_at as f64),
            parent,
        ])?
        .run()
        .await?;
    let id = result
        .meta()?
        .and_then(|m| m.last_row_id)
        .ok_or_else(|| worker::Error::RustError("insert post: no last_row_id".into()))?;
    Ok(id)
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

async fn update_post_body(db: &D1Database, id: i64, body: &str) -> Result<()> {
    db.prepare("UPDATE posts SET body = ?1 WHERE id = ?2")
        .bind(&[JsValue::from_str(body), JsValue::from_f64(id as f64)])?
        .run()
        .await?;
    Ok(())
}

async fn delete_post(db: &D1Database, id: i64) -> Result<Vec<String>> {
    let imgs = images_for_posts(db, &[id]).await?;
    let keys = imgs
        .into_iter()
        .flat_map(|(_, v)| v.into_iter().map(|i| i.r2_key))
        .collect();
    db.prepare("DELETE FROM posts WHERE id = ?1")
        .bind(&[JsValue::from_f64(id as f64)])?
        .run()
        .await?;
    Ok(keys)
}

async fn subscriber_exists(db: &D1Database, email: &str) -> Result<bool> {
    let row = db
        .prepare("SELECT COUNT(*) AS n FROM subscribers WHERE email = ?1")
        .bind(&[JsValue::from_str(email)])?
        .first::<CountRow>(None)
        .await?;
    Ok(row.map(|r| r.n > 0).unwrap_or(false))
}

async fn insert_interested(db: &D1Database, email: &str, created_at: i64) -> Result<()> {
    db.prepare(
        "INSERT INTO subscribers (email, status, token, created_at)
         VALUES (?1, 'pending', '', ?2)",
    )
    .bind(&[
        JsValue::from_str(email),
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
    Ok(Credential {
        id: row.credential_id,
        public_key,
        counter: row.counter as u32,
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
    let blob = D1Type::Blob(public_key);
    let id = D1Type::Text(credential_id);
    let counter = D1Type::Integer(counter as i32);
    let transports = match &transports {
        Some(s) => D1Type::Text(s),
        None => D1Type::Null,
    };
    let label_t = D1Type::Text(label);
    let created = D1Type::Real(created_at as f64);
    db.prepare(
        "INSERT INTO credentials (credential_id, public_key, counter, transports, label, created_at)
         VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
    )
    .bind_refs([&id, &blob, &counter, &transports, &label_t, &created])?
    .run()
    .await?;
    Ok(())
}

async fn update_counter(db: &D1Database, credential_id: &str, counter: u32) -> Result<()> {
    db.prepare("UPDATE credentials SET counter = ?1 WHERE credential_id = ?2")
        .bind(&[
            JsValue::from_f64(counter as f64),
            JsValue::from_str(credential_id),
        ])?
        .run()
        .await?;
    Ok(())
}

async fn delete_credential(db: &D1Database, id: i64) -> Result<()> {
    db.prepare("DELETE FROM credentials WHERE id = ?1")
        .bind(&[JsValue::from_f64(id as f64)])?
        .run()
        .await?;
    Ok(())
}
