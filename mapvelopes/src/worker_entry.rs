//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! Thin glue: read `GOOGLE_MAPS_API_KEY`, classify the request, fetch Google
//! Maps when the key is usable, and return HTML, JSON, or a PDF.

use worker::{event, Context, Env, Fetch, Headers, Method, Request, Response, Result, Url};

use crate::address::Address;
use crate::api::{self, Classified};
use crate::error::Error;
use crate::maps::{
    api_key_usable, directions_url, geocode_url, looks_like_jpeg, spec_from_google, static_map_url,
    EnvelopeSpec,
};
use crate::render;

#[event(fetch)]
async fn fetch(mut req: Request, env: Env, _ctx: Context) -> Result<Response> {
    let key = read_maps_key(&env);
    let maps_live = api_key_usable(key.as_deref());

    let url = req.url()?;
    let query: Vec<(String, String)> = url
        .query_pairs()
        .map(|(k, v)| (k.into_owned(), v.into_owned()))
        .collect();
    let content_type = req.headers().get("Content-Type").ok().flatten();
    let body = if req.method() == Method::Post {
        req.bytes().await.unwrap_or_default()
    } else {
        Vec::new()
    };

    let classified = api::classify(&api::ApiRequest {
        method: req.method().as_ref().to_string(),
        path: url.path().to_string(),
        query,
        content_type,
        body,
    });

    match classified {
        Classified::Health => json(200, api::health_json(maps_live)),
        Classified::Form => html(api::form_html(maps_live)),
        Classified::NotFound => json_error(&Error::BadRequest("not found".into()), 404),
        Classified::BadRequest(msg) => json_error(&Error::BadRequest(msg), 400),
        Classified::Envelope { from, to } => match build_spec(&from, &to, key.as_deref()).await {
            Ok(spec) => match render::render(&spec) {
                Ok(pdf) => pdf_response(pdf),
                Err(err) => json_error(&err, err.status()),
            },
            Err(err) => json_error(&err, err.status()),
        },
    }
}

fn read_maps_key(env: &Env) -> Option<String> {
    env.secret("GOOGLE_MAPS_API_KEY")
        .map(|s| s.to_string())
        .or_else(|_| env.var("GOOGLE_MAPS_API_KEY").map(|v| v.to_string()))
        .ok()
}

async fn build_spec(
    from: &str,
    to: &str,
    key: Option<&str>,
) -> std::result::Result<EnvelopeSpec, Error> {
    let from = Address::parse_named("from", from)?;
    let to = Address::parse_named("to", to)?;
    if !api_key_usable(key) {
        return Ok(EnvelopeSpec::schematic(from, to));
    }
    let key = key.expect("usable key");
    live_spec(from, to, key).await
}

async fn live_spec(
    from: Address,
    to: Address,
    key: &str,
) -> std::result::Result<EnvelopeSpec, Error> {
    let from_body = fetch_bytes(&geocode_url(&from.geocode_query(), key)).await?;
    let to_body = fetch_bytes(&geocode_url(&to.geocode_query(), key)).await?;
    let from_ll = crate::maps::parse_geocode(&from_body)?;
    let to_ll = crate::maps::parse_geocode(&to_body)?;
    let dir_body = fetch_bytes(&directions_url(from_ll, to_ll, key)).await?;
    let route = crate::maps::parse_directions(&dir_body)?;
    let jpeg = match fetch_bytes(&static_map_url(&route, key)).await {
        Ok(bytes) if looks_like_jpeg(&bytes) => Some(bytes),
        Ok(_) | Err(_) => None,
    };
    spec_from_google(from, to, &from_body, &to_body, &dir_body, jpeg.as_deref())
}

async fn fetch_bytes(url: &str) -> std::result::Result<Vec<u8>, Error> {
    let parsed = Url::parse(url).map_err(|e| Error::Maps(format!("url: {e}")))?;
    let mut resp = Fetch::Url(parsed)
        .send()
        .await
        .map_err(|e| Error::Maps(format!("fetch: {e}")))?;
    let status = resp.status_code();
    let bytes = resp
        .bytes()
        .await
        .map_err(|e| Error::Maps(format!("read: {e}")))?;
    if status >= 400 {
        if let Some(msg) = crate::maps::static_map_error(&bytes) {
            return Err(Error::Maps(msg));
        }
        return Err(Error::Maps(format!("HTTP {status}")));
    }
    Ok(bytes)
}

fn pdf_response(pdf: Vec<u8>) -> Result<Response> {
    let headers = Headers::new();
    let _ = headers.set("Content-Type", "application/pdf");
    let _ = headers.set("Content-Disposition", "inline; filename=\"envelope.pdf\"");
    Ok(Response::from_bytes(pdf)?
        .with_status(200)
        .with_headers(headers))
}

fn html(body: Vec<u8>) -> Result<Response> {
    let headers = Headers::new();
    let _ = headers.set("Content-Type", "text/html; charset=utf-8");
    Ok(Response::from_bytes(body)?
        .with_status(200)
        .with_headers(headers))
}

fn json(status: u16, body: Vec<u8>) -> Result<Response> {
    let headers = Headers::new();
    let _ = headers.set("Content-Type", "application/json");
    Ok(Response::from_bytes(body)?
        .with_status(status)
        .with_headers(headers))
}

fn json_error(err: &Error, status: u16) -> Result<Response> {
    json(status, api::error_json(err))
}
