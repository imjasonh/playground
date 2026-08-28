//! Transport-agnostic HTTP routing.
//!
//! The same router serves the Workers entry point, the native integration
//! test server, and the benchmarks. Routes:
//!
//! | Route | Purpose |
//! |---|---|
//! | `GET /<repo>/info/refs?service=…` | smart-HTTP advertisement |
//! | `POST /<repo>/git-upload-pack` | fetch (protocol v2) |
//! | `POST /<repo>/git-receive-pack` | push |
//! | `GET /api/<repo>` | repo status: state, timestamps, lease, size |
//! | `GET /api/<repo>/refs` | JSON ref listing |
//! | `GET /api/<repo>/file/<refish>/<path>` | raw file contents |
//! | `GET /api/<repo>/tree/<refish>/<path>` | JSON dir listing + last-commit |
//! | `GET /api/<repo>/blame/<refish>/<path>` | JSON line-level blame |
//! | `POST /api/<repo>/repack` | run pack consolidation now |
//! | `POST /api/<repo>/loadtest` | budget-capped push/pull load test |
//! | `GET /loadtest` | phone-friendly HTML loadtest (use `?run=1` to start) |

use crate::protocol::{self, BodyStream, BufferedBody};
use crate::refs::StateStore;
use crate::repo::Repo;
use crate::storage::Store;
use serde_json::json;

/// A parsed inbound request.
pub struct Request<'a> {
    pub method: &'a str,
    /// Path without query string.
    pub path: &'a str,
    /// Raw query string (no leading `?`), if any.
    pub query: Option<&'a str>,
    /// Value of the `Git-Protocol` header, if present.
    pub git_protocol: Option<&'a str>,
    /// Value of the `Content-Encoding` header, if present (git's HTTP client
    /// gzips larger negotiation bodies).
    pub content_encoding: Option<&'a str>,
    /// Cloudflare `CF-Ray` for this request, when the edge supplied one.
    /// Surfaced in structured logs and side-band progress for correlation
    /// with Workers Traces.
    pub cf_ray: Option<&'a str>,
    /// `X-Loadtest-Token` header value, if present.
    pub loadtest_token: Option<&'a str>,
}

/// A response body: fully materialized, or streamed in chunks.
///
/// Streaming is not an optimization here — it is a *correctness* requirement:
/// the Workers isolate has a hard 128 MiB memory limit (exceeding it is
/// Cloudflare error 1102; clients see a 503), so any body proportional to
/// repo size must never be resident at once. `tests/memory.rs` enforces this
/// in CI with a tracking allocator.
pub enum Body {
    Full(Vec<u8>),
    /// Chunks are yielded in order; an `Err` aborts the response mid-stream
    /// (git clients detect the truncated pkt-line/pack framing).
    Stream(futures::stream::LocalBoxStream<'static, Result<Vec<u8>, String>>),
}

impl Body {
    /// Length if fully materialized.
    pub fn len_if_full(&self) -> Option<usize> {
        match self {
            Body::Full(b) => Some(b.len()),
            Body::Stream(_) => None,
        }
    }

    /// Drain to a single buffer (test/benchmark harnesses; native servers
    /// that don't stream).
    pub async fn into_bytes(self) -> Result<Vec<u8>, String> {
        use futures::StreamExt;
        match self {
            Body::Full(b) => Ok(b),
            Body::Stream(mut s) => {
                let mut out = Vec::new();
                while let Some(chunk) = s.next().await {
                    out.extend_from_slice(&chunk?);
                }
                Ok(out)
            }
        }
    }
}

/// Response to relay to the transport.
pub struct Response {
    pub status: u16,
    pub content_type: String,
    pub body: Body,
    /// Request metrics and total handler milliseconds, populated by
    /// [`GitHttp::handle`]. Transports emit these as a `Server-Timing`
    /// header and/or a structured log line. For streamed bodies these cover
    /// the handler phase only (backend ops that occur while the body
    /// streams are not yet accounted; noted in docs/design.md).
    pub metrics: Option<(crate::metrics::Metrics, f64)>,
}

impl Response {
    fn ok(content_type: &str, body: Vec<u8>) -> Response {
        Response {
            status: 200,
            content_type: content_type.to_string(),
            body: Body::Full(body),
            metrics: None,
        }
    }

    fn streamed(
        content_type: &str,
        stream: futures::stream::LocalBoxStream<'static, Result<Vec<u8>, String>>,
    ) -> Response {
        Response {
            status: 200,
            content_type: content_type.to_string(),
            body: Body::Stream(stream),
            metrics: None,
        }
    }

    fn json(status: u16, value: serde_json::Value) -> Response {
        Response {
            status,
            content_type: "application/json".to_string(),
            body: Body::Full(value.to_string().into_bytes()),
            metrics: None,
        }
    }

    /// The `Server-Timing` header value for this response, if metrics were
    /// collected.
    pub fn server_timing(&self) -> Option<String> {
        self.metrics
            .as_ref()
            .map(|(m, total)| m.server_timing(*total))
    }

    fn error(status: u16, message: &str) -> Response {
        Response::json(status, json!({ "error": message }))
    }
}

/// Default per-push body limit: Cloudflare's HTTP request-body cap on
/// Free/Pro zones (decimal 100 MB). In production over-limit pushes are
/// 413'd at the edge before the Worker runs; enforcing the same number here
/// keeps local harnesses and CI honest about it (see docs/design.md "Size
/// limits").
pub const DEFAULT_PUSH_LIMIT_BYTES: u64 = 100_000_000;

/// The server: byte store + state store. Held by `Rc` so streamed response
/// bodies (which outlive the request handler) can own what they read from.
pub struct GitHttp {
    pub store: std::rc::Rc<dyn Store>,
    pub states: std::rc::Rc<dyn StateStore>,
    /// Per-push body limit ([`DEFAULT_PUSH_LIMIT_BYTES`] unless overridden —
    /// e.g. raised on Business/Enterprise zones, lowered in tests).
    pub push_limit_bytes: u64,
    /// When set, `GET /loadtest` and `POST /api/…/loadtest` require this
    /// exact token (query `token=`, header `X-Loadtest-Token`, or JSON
    /// `"token"`). `None` leaves loadtests open (native tests).
    pub loadtest_token: Option<String>,
    /// When true (Worker), a missing [`Self::loadtest_token`] rejects
    /// loadtests with 503 instead of running open.
    pub loadtest_auth_required: bool,
    /// Optional HTTP self-fetch for multi-repo / multi-shard loadtests.
    pub loadtest_fanout: Option<std::rc::Rc<dyn crate::loadtest::LoadtestFanout>>,
}

impl GitHttp {
    pub fn new(store: std::rc::Rc<dyn Store>, states: std::rc::Rc<dyn StateStore>) -> GitHttp {
        GitHttp {
            store,
            states,
            push_limit_bytes: DEFAULT_PUSH_LIMIT_BYTES,
            loadtest_token: None,
            loadtest_auth_required: false,
            loadtest_fanout: None,
        }
    }

    pub fn with_push_limit(mut self, bytes: u64) -> GitHttp {
        self.push_limit_bytes = bytes;
        self
    }

    pub fn with_loadtest_token(mut self, token: impl Into<String>) -> GitHttp {
        self.loadtest_token = Some(token.into());
        self.loadtest_auth_required = true;
        self
    }

    /// Worker: require a token, but the secret is not configured yet.
    pub fn with_loadtest_auth_required(mut self) -> GitHttp {
        self.loadtest_auth_required = true;
        self
    }

    /// Attach a self-fetch fan-out (Worker only).
    pub fn with_loadtest_fanout(
        mut self,
        fanout: std::rc::Rc<dyn crate::loadtest::LoadtestFanout>,
    ) -> GitHttp {
        self.loadtest_fanout = Some(fanout);
        self
    }
}

fn query_param<'q>(query: Option<&'q str>, key: &str) -> Option<&'q str> {
    query?
        .split('&')
        .filter_map(|kv| kv.split_once('='))
        .find(|(k, _)| *k == key)
        .map(|(_, v)| v)
}

/// Minimal query-component decode (`%XX` and `+` → space). Hex tokens need
/// no decoding; this keeps pasted tokens with accidental encoding working.
fn percent_decode(s: &str) -> String {
    let mut out = Vec::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b'%' if i + 2 < bytes.len() => {
                let h = |c: u8| -> Option<u8> {
                    match c {
                        b'0'..=b'9' => Some(c - b'0'),
                        b'a'..=b'f' => Some(c - b'a' + 10),
                        b'A'..=b'F' => Some(c - b'A' + 10),
                        _ => None,
                    }
                };
                if let (Some(hi), Some(lo)) = (h(bytes[i + 1]), h(bytes[i + 2])) {
                    out.push((hi << 4) | lo);
                    i += 3;
                } else {
                    out.push(bytes[i]);
                    i += 1;
                }
            }
            b => {
                out.push(b);
                i += 1;
            }
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// Repo names are a single path segment: no traversal, no separators.
fn valid_repo_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 100
        && name != "."
        && name != ".."
        && !name.starts_with('.')
        && name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
}

impl GitHttp {
    fn repo<'r>(&'r self, name: &'r str) -> Repo<'r> {
        Repo {
            store: self.store.as_ref(),
            states: self.states.as_ref(),
            name,
        }
    }

    /// Handle one request. `nonce` must be unique per request (used to name
    /// staged pack uploads); the caller supplies randomness because this
    /// crate is runtime-agnostic.
    ///
    /// Collects request metrics (backend op counts, phase timings, bytes)
    /// and attaches them to the response for the transport to emit.
    pub async fn handle(
        &self,
        req: &Request<'_>,
        body: &mut dyn BodyStream,
        nonce: &str,
    ) -> Response {
        crate::metrics::begin();
        if let Some(ray) = req.cf_ray {
            crate::trace::set_ray(Some(ray.to_string()));
        }
        let start = crate::metrics::now_ms();
        let mut resp = self.route(req, body, nonce).await;
        let total_ms = crate::metrics::now_ms() - start;
        match &resp.body {
            // Streamed bodies (fetch packs) keep writing after headers leave.
            // Snapshot for the Server-Timing header, but leave the collector
            // live so the packfile PROGRESS tail can emit a full timing line.
            Body::Stream(_) => {
                if let Some(m) = crate::metrics::snapshot() {
                    resp.metrics = Some((m, total_ms));
                }
            }
            Body::Full(bytes) => {
                if let Some(mut m) = crate::metrics::take() {
                    m.bytes_out += bytes.len() as u64;
                    resp.metrics = Some((m, total_ms));
                }
            }
        }
        resp
    }

    async fn route(&self, req: &Request<'_>, body: &mut dyn BodyStream, nonce: &str) -> Response {
        let segments: Vec<&str> = req.path.split('/').filter(|s| !s.is_empty()).collect();
        match segments.as_slice() {
            ["api", repo, "loadtest"] if req.method == "POST" && valid_repo_name(repo) => {
                self.api_loadtest(req, strip_git(repo), body).await
            }
            ["loadtest"] if req.method == "GET" => self.phone_loadtest(req).await,
            ["api", rest @ ..] => self.handle_api(req, rest, nonce).await,
            [repo, "info", "refs"] if req.method == "GET" => {
                self.info_refs(req, strip_git(repo)).await
            }
            [repo, "git-upload-pack"] if req.method == "POST" => {
                self.upload_pack(strip_git(repo), body, req.content_encoding)
                    .await
            }
            [repo, "git-receive-pack"] if req.method == "POST" => {
                if req.content_encoding.map(is_gzip).unwrap_or(false) {
                    // Pushes stream to R2; a compressed body would defeat
                    // that. git never gzips receive-pack bodies (it streams
                    // them chunked), so just reject.
                    return Response::error(415, "compressed push bodies are not supported");
                }
                self.receive_pack(strip_git(repo), body, nonce).await
            }
            [] => Response::ok(
                "text/plain",
                b"git: a git smart-HTTP server on Cloudflare Workers\n".to_vec(),
            ),
            _ => Response::error(404, "not found"),
        }
    }

    async fn info_refs(&self, req: &Request<'_>, repo_name: &str) -> Response {
        if !valid_repo_name(repo_name) {
            return Response::error(400, "invalid repo name");
        }
        let repo = self.repo(repo_name);
        match query_param(req.query, "service") {
            Some("git-upload-pack") => {
                // Fetch requires protocol v2 (git ≥ 2.26's default).
                let v2 = req
                    .git_protocol
                    .map(|v| v.contains("version=2"))
                    .unwrap_or(false);
                if !v2 {
                    return Response::error(
                        400,
                        "this server requires git protocol v2 (git >= 2.26)",
                    );
                }
                Response::ok(
                    "application/x-git-upload-pack-advertisement",
                    protocol::advertise_upload_pack_v2(),
                )
            }
            Some("git-receive-pack") => match repo.load_state().await {
                Ok(loaded) => Response::ok(
                    "application/x-git-receive-pack-advertisement",
                    protocol::advertise_receive_pack(&loaded.state),
                ),
                Err(e) => Response::error(500, &e),
            },
            _ => Response::error(400, "dumb HTTP protocol is not supported"),
        }
    }

    async fn upload_pack(
        &self,
        repo_name: &str,
        body: &mut dyn BodyStream,
        content_encoding: Option<&str>,
    ) -> Response {
        if !valid_repo_name(repo_name) {
            return Response::error(400, "invalid repo name");
        }
        // Negotiation bodies are tiny; buffer them.
        let mut buf = Vec::new();
        loop {
            match body.next_chunk().await {
                Ok(Some(c)) => buf.extend_from_slice(&c),
                Ok(None) => break,
                Err(e) => return Response::error(400, &e),
            }
        }
        if content_encoding.map(is_gzip).unwrap_or(false) {
            buf = match gunzip(&buf) {
                Ok(b) => b,
                Err(e) => return Response::error(400, &e),
            };
        }
        match protocol::upload_pack(self.store.clone(), self.states.clone(), repo_name, &buf).await
        {
            Ok(body) => Response {
                status: 200,
                content_type: "application/x-git-upload-pack-result".to_string(),
                body,
                metrics: None,
            },
            Err(e) => Response::error(500, &e),
        }
    }

    async fn receive_pack(
        &self,
        repo_name: &str,
        body: &mut dyn BodyStream,
        nonce: &str,
    ) -> Response {
        if !valid_repo_name(repo_name) {
            return Response::error(400, "invalid repo name");
        }
        let repo = self.repo(repo_name);
        let now_ms = crate::metrics::now_ms() as i64;
        match protocol::receive_pack(&repo, body, nonce, self.push_limit_bytes, now_ms).await {
            Ok(out) => Response::ok("application/x-git-receive-pack-result", out),
            Err(e) => Response::error(500, &e),
        }
    }

    async fn handle_api(&self, req: &Request<'_>, rest: &[&str], nonce: &str) -> Response {
        let (repo_name, rest) = match rest {
            [repo, rest @ ..] if valid_repo_name(repo) => (*repo, rest),
            _ => return Response::error(400, "invalid repo name"),
        };
        let repo = self.repo(repo_name);
        match (req.method, rest) {
            ("GET", ["refs"]) => match repo.load_state().await {
                Ok(loaded) => Response::json(
                    200,
                    json!({ "head": loaded.state.head, "refs": loaded.state.refs }),
                ),
                Err(e) => Response::error(500, &e),
            },
            ("GET", []) => self.api_status(&repo).await,
            ("POST", ["repack"]) => match crate::maintenance::repack(&repo, nonce).await {
                Ok(outcome) => Response::json(200, json!({ "result": format!("{outcome:?}") })),
                Err(e) => Response::error(500, &e),
            },
            ("GET", ["file", refish, path @ ..]) => {
                self.api_file(&repo, refish, &path.join("/")).await
            }
            ("GET", ["tree", refish, path @ ..]) => {
                self.api_tree(&repo, refish, &path.join("/")).await
            }
            ("GET", ["blame", refish, path @ ..]) => {
                self.api_blame(&repo, refish, &path.join("/")).await
            }
            _ => Response::error(404, "not found"),
        }
    }

    /// `GET /api/<repo>` — repository summary: state, default branch,
    /// last-push / last-repack times, maintenance lease, and size counters.
    ///
    /// `state` is `EMPTY` (never pushed) or `READY` today. Once the migration
    /// importer (`docs/large-repo-migration.md`) exists, an in-progress import
    /// reports `MIGRATING` here with progress fields; the shape is designed to
    /// carry that without breaking existing consumers.
    async fn api_status(&self, repo: &Repo<'_>) -> Response {
        let loaded = match repo.load_state().await {
            Ok(s) => s,
            Err(e) => return Response::error(500, &e),
        };
        let state = &loaded.state;
        let empty = state.packs.is_empty() && state.refs.is_empty();
        // Default branch: HEAD's symref target with the refs/heads/ prefix
        // stripped, when it points at a local branch.
        let default_branch = state
            .head
            .strip_prefix("refs/heads/")
            .map(|s| s.to_string());
        let objects: u64 = state.packs.iter().map(|p| p.objects).sum();
        let bytes: u64 = state.packs.iter().map(|p| p.bytes).sum();
        let now_ms = crate::metrics::now_ms() as i64;
        let lease_held = loaded.lease_until_ms > now_ms;
        Response::json(
            200,
            json!({
                "status": if empty { "EMPTY" } else { "READY" },
                "head": state.head,
                "default_branch": default_branch,
                "head_commit": state.head_oid(),
                "last_push": state.last_push_ms.map(crate::timefmt::rfc3339_ms),
                "last_repack": state.last_repack_ms.map(crate::timefmt::rfc3339_ms),
                "repack_lease_until": if lease_held {
                    Some(crate::timefmt::rfc3339_ms(loaded.lease_until_ms))
                } else {
                    None
                },
                "refs": state.refs.len(),
                "packs": state.packs.len(),
                "retired": state.retired.len(),
                "objects": objects,
                "bytes": bytes,
                "version": loaded.version,
            }),
        )
    }

    /// `POST /api/<repo>/loadtest` — budget-capped concurrent push/pull load
    /// test. Nested protocol calls reset the request metrics collector, so the
    /// response body's report is the source of truth (Server-Timing on this
    /// response only covers coordination overhead).
    async fn api_loadtest(
        &self,
        req: &Request<'_>,
        repo_name: &str,
        body: &mut dyn BodyStream,
    ) -> Response {
        let mut buf = Vec::new();
        loop {
            match body.next_chunk().await {
                Ok(Some(c)) => buf.extend_from_slice(&c),
                Ok(None) => break,
                Err(e) => return Response::error(400, &e),
            }
        }
        if buf.is_empty() {
            return Response::error(
                400,
                "JSON body required: {\"confirm\":true,\"budget_usd\":0.1,…}",
            );
        }
        let parsed: crate::loadtest::LoadTestRequest = match serde_json::from_slice(&buf) {
            Ok(r) => r,
            Err(e) => return Response::error(400, &format!("bad loadtest JSON: {e}")),
        };
        let provided = req
            .loadtest_token
            .or(query_param(req.query, "token"))
            .or(parsed.token.as_deref());
        if let Some(deny) = self.loadtest_auth_error(provided) {
            return deny;
        }
        let cfg = match parsed.into_config() {
            Ok(c) => c,
            Err(e) => return Response::error(400, &e),
        };

        let http = self.coordinator_http();
        let report = match crate::loadtest::execute(&http, repo_name, &cfg).await {
            Ok(r) => r,
            Err(e) => return Response::error(500, &e),
        };

        match serde_json::to_vec_pretty(&report) {
            Ok(bytes) => Response::ok("application/json", bytes),
            Err(e) => Response::error(500, &e.to_string()),
        }
    }

    /// `GET /loadtest` — phone-friendly HTML. Without `run=1`, shows a
    /// landing page with budget / peak / repos controls. With `run=1`, runs a
    /// budget-capped load test into disposable repo(s) and prints the report.
    /// Query knobs: `budget`, `peak` (writers per repo), `repos` (parallel
    /// DOs), `duration` (seconds per stage), `token`.
    async fn phone_loadtest(&self, req: &Request<'_>) -> Response {
        let query = req.query;
        let budget = query_param(query, "budget")
            .and_then(|s| s.parse::<f64>().ok())
            .unwrap_or(crate::loadtest::PHONE_DEFAULT_BUDGET_USD)
            .clamp(0.01, crate::loadtest::MAX_BUDGET_USD);
        let duration = query_param(query, "duration")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(crate::loadtest::PHONE_DEFAULT_DURATION_SECS)
            .clamp(1, crate::loadtest::MAX_DURATION_SECS);
        let peak = query_param(query, "peak")
            .and_then(|s| s.parse::<u32>().ok())
            .unwrap_or(crate::loadtest::PHONE_DEFAULT_PEAK);
        let peak = crate::loadtest::clamp_phone_peak(peak);
        let repos = query_param(query, "repos")
            .and_then(|s| s.parse::<u32>().ok())
            .unwrap_or(crate::loadtest::PHONE_DEFAULT_REPOS);
        let repos = crate::loadtest::clamp_phone_repos(repos);
        let token = req
            .loadtest_token
            .or(query_param(query, "token"))
            .map(percent_decode);
        let token = token.as_deref();

        let run = query_param(query, "run")
            .map(|s| s == "1" || s.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
        if !run {
            return Response::ok(
                "text/html; charset=utf-8",
                crate::loadtest::html_landing(budget, duration, peak, repos, token).into_bytes(),
            );
        }
        if let Some(deny) = self.loadtest_auth_error(token) {
            let msg = match deny.status {
                503 => "LOADTEST_TOKEN secret is not configured on this Worker.",
                _ => "Missing or invalid token. Open /loadtest?token=YOUR_TOKEN",
            };
            return Response::ok(
                "text/html; charset=utf-8",
                format!(
                    "<!doctype html><meta name=viewport content=\"width=device-width,initial-scale=1\">\
                     <pre style=\"padding:1.5rem;font:1rem sans-serif\">{msg}</pre>"
                )
                .into_bytes(),
            );
        }

        let repo = crate::loadtest::phone_repo_name();
        let phone_req = crate::loadtest::phone_request(budget, duration, peak, repos);
        let cfg = match phone_req.into_config() {
            Ok(c) => c,
            Err(e) => {
                return Response::ok(
                    "text/html; charset=utf-8",
                    format!("<pre>bad config: {e}</pre>").into_bytes(),
                );
            }
        };
        let http = self.coordinator_http();
        match crate::loadtest::execute(&http, &repo, &cfg).await {
            Ok(report) => Response::ok(
                "text/html; charset=utf-8",
                crate::loadtest::html_report(&report, token, peak, duration).into_bytes(),
            ),
            Err(e) => Response::ok(
                "text/html; charset=utf-8",
                format!("<pre>loadtest failed: {e}</pre>").into_bytes(),
            ),
        }
    }

    /// Keep fan-out so multi-repo / multi-shard runs can self-fetch.
    fn coordinator_http(&self) -> GitHttp {
        let mut http = GitHttp::new(self.store.clone(), self.states.clone())
            .with_push_limit(self.push_limit_bytes);
        http.loadtest_auth_required = false;
        http.loadtest_token = None;
        http.loadtest_fanout = self.loadtest_fanout.clone();
        http
    }

    /// `None` = authorized. `Some(response)` = reject.
    fn loadtest_auth_error(&self, provided: Option<&str>) -> Option<Response> {
        if !self.loadtest_auth_required && self.loadtest_token.is_none() {
            return None;
        }
        let Some(expected) = self.loadtest_token.as_deref() else {
            return Some(Response::error(
                503,
                "LOADTEST_TOKEN secret is not configured",
            ));
        };
        if !crate::loadtest::token_matches(provided.unwrap_or(""), expected) {
            return Some(Response::error(401, "invalid or missing loadtest token"));
        }
        None
    }

    async fn api_file(&self, repo: &Repo<'_>, refish: &str, path: &str) -> Response {
        match self.resolve(repo, refish).await {
            Ok((_state, odb, commit)) => {
                match crate::fileapi::file_contents(&odb, commit, path).await {
                    // Large blobs are chunked out of one shared buffer rather
                    // than copied whole into the response (and again into the
                    // JS body) - a third of the peak memory for big files.
                    Ok(Some(data)) => Response::streamed(
                        "application/octet-stream",
                        chunk_shared(std::rc::Rc::new(data)),
                    ),
                    Ok(None) => Response::error(404, "no such file at that ref"),
                    Err(e) => Response::error(500, &e),
                }
            }
            Err(resp) => resp,
        }
    }

    async fn api_tree(&self, repo: &Repo<'_>, refish: &str, path: &str) -> Response {
        match self.resolve(repo, refish).await {
            Ok((state, odb, commit)) => {
                // Load only the file-log shards covering this directory.
                let prefix = if path.is_empty() {
                    String::new()
                } else {
                    format!("{path}/")
                };
                let scope = crate::repo::FilelogScope::Prefix(&prefix);
                let segments = match load_filelog(repo, &state, &scope).await {
                    Ok(s) => s,
                    Err(resp) => return resp,
                };
                match crate::fileapi::list_tree(&odb, &segments, commit, path).await {
                    Ok(Some(entries)) => Response::json(
                        200,
                        json!({ "commit": commit.to_hex(), "path": path, "entries": entries }),
                    ),
                    Ok(None) => Response::error(404, "no such directory at that ref"),
                    Err(e) => Response::error(500, &e),
                }
            }
            Err(resp) => resp,
        }
    }

    async fn api_blame(&self, repo: &Repo<'_>, refish: &str, path: &str) -> Response {
        match self.resolve(repo, refish).await {
            Ok((state, odb, commit)) => {
                // Blame needs only the shard(s) containing this exact path.
                let scope = crate::repo::FilelogScope::Path(path);
                let segments = match load_filelog(repo, &state, &scope).await {
                    Ok(s) => s,
                    Err(resp) => return resp,
                };
                match crate::blame::blame(&odb, &segments, commit, path).await {
                    Ok(Some(lines)) => Response::json(
                        200,
                        json!({ "commit": commit.to_hex(), "path": path, "lines": lines }),
                    ),
                    Ok(None) => Response::error(404, "no blame for that path"),
                    Err(e) => Response::error(500, &e),
                }
            }
            Err(resp) => resp,
        }
    }

    /// Shared API preamble: load state, open the odb, resolve the refish.
    async fn resolve<'r>(
        &self,
        repo: &'r Repo<'r>,
        refish: &str,
    ) -> Result<
        (
            crate::refs::RepoState,
            crate::odb::Odb<'r>,
            crate::object::Oid,
        ),
        Response,
    > {
        let loaded = repo
            .load_state()
            .await
            .map_err(|e| Response::error(500, &e))?;
        let state = loaded.state;
        if state.packs.is_empty() {
            return Err(Response::error(404, "repository is empty"));
        }
        let odb = repo
            .odb(&state)
            .await
            .map_err(|e| Response::error(500, &e))?;
        let commit = crate::fileapi::resolve_refish(&state, &odb, refish)
            .await
            .map_err(|e| Response::error(404, &e))?;
        Ok((state, odb, commit))
    }
}

/// Allow both `/repo` and `/repo.git` remote URLs.
fn strip_git(name: &str) -> &str {
    name.strip_suffix(".git").unwrap_or(name)
}

/// Load scoped file-log segments, mapping failure to a 500 response
/// (shared by the tree and blame APIs).
async fn load_filelog(
    repo: &Repo<'_>,
    state: &crate::refs::RepoState,
    scope: &crate::repo::FilelogScope<'_>,
) -> Result<Vec<crate::repo::FileLogSegment>, Response> {
    crate::repo::load_filelog_scoped(repo.store, repo.name, state, scope)
        .await
        .map_err(|e| Response::error(500, &e))
}

/// Response-body chunk size for streamed blobs (matches the pack emitter's
/// chunking; bounds each transient copy).
const STREAM_CHUNK: usize = 1024 * 1024;

/// Stream a shared buffer as [`STREAM_CHUNK`]-sized chunks (each chunk is a
/// transient copy; the buffer itself stays resident exactly once).
fn chunk_shared(
    data: std::rc::Rc<Vec<u8>>,
) -> futures::stream::LocalBoxStream<'static, Result<Vec<u8>, String>> {
    use futures::StreamExt;
    futures::stream::unfold((data, 0usize), |(data, start)| async move {
        if start >= data.len() {
            return None;
        }
        let end = (start + STREAM_CHUNK).min(data.len());
        let chunk = data[start..end].to_vec();
        Some((Ok(chunk), (data, end)))
    })
    .boxed_local()
}

fn is_gzip(encoding: &str) -> bool {
    encoding.eq_ignore_ascii_case("gzip") || encoding.eq_ignore_ascii_case("x-gzip")
}

fn gunzip(data: &[u8]) -> Result<Vec<u8>, String> {
    use std::io::Read;
    let mut out = Vec::new();
    flate2::read::GzDecoder::new(data)
        .read_to_end(&mut out)
        .map_err(|e| format!("bad gzip body: {e}"))?;
    Ok(out)
}

// Re-export for transports.
pub use crate::protocol::BodyStream as RequestBody;

/// Convenience for transports that buffer the whole body.
pub fn buffered(bytes: Vec<u8>) -> BufferedBody {
    BufferedBody::new(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repo_name_validation() {
        assert!(valid_repo_name("my-repo"));
        assert!(valid_repo_name("repo_1.x"));
        assert!(!valid_repo_name(""));
        assert!(!valid_repo_name(".."));
        assert!(!valid_repo_name(".hidden"));
        assert!(!valid_repo_name("a/b"));
        assert!(!valid_repo_name("a b"));
    }

    #[test]
    fn query_parsing() {
        assert_eq!(
            query_param(Some("service=git-upload-pack"), "service"),
            Some("git-upload-pack")
        );
        assert_eq!(query_param(Some("a=1&b=2"), "b"), Some("2"));
        assert_eq!(query_param(None, "x"), None);
    }
}
