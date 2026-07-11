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
//! | `GET /api/<repo>/refs` | JSON ref listing |
//! | `GET /api/<repo>/status` | repo status: state, default branch, last push, size |
//! | `GET /api/<repo>/file/<refish>/<path>` | raw file contents |
//! | `GET /api/<repo>/tree/<refish>/<path>` | JSON dir listing + last-commit |
//! | `GET /api/<repo>/blame/<refish>/<path>` | JSON line-level blame |
//! | `POST /api/<repo>/repack` | run pack consolidation now |

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
}

impl GitHttp {
    pub fn new(store: std::rc::Rc<dyn Store>, states: std::rc::Rc<dyn StateStore>) -> GitHttp {
        GitHttp {
            store,
            states,
            push_limit_bytes: DEFAULT_PUSH_LIMIT_BYTES,
        }
    }

    pub fn with_push_limit(mut self, bytes: u64) -> GitHttp {
        self.push_limit_bytes = bytes;
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
        let start = crate::metrics::now_ms();
        let mut resp = self.route(req, body, nonce).await;
        let total_ms = crate::metrics::now_ms() - start;
        if let Some(mut m) = crate::metrics::take() {
            if let Some(n) = resp.body.len_if_full() {
                m.bytes_out += n as u64;
            }
            resp.metrics = Some((m, total_ms));
        }
        resp
    }

    async fn route(&self, req: &Request<'_>, body: &mut dyn BodyStream, nonce: &str) -> Response {
        let segments: Vec<&str> = req.path.split('/').filter(|s| !s.is_empty()).collect();
        match segments.as_slice() {
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
                Ok((state, _)) => Response::ok(
                    "application/x-git-receive-pack-advertisement",
                    protocol::advertise_receive_pack(&state),
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
                Ok((state, _)) => {
                    Response::json(200, json!({ "head": state.head, "refs": state.refs }))
                }
                Err(e) => Response::error(500, &e),
            },
            ("GET", ["status"]) => self.api_status(&repo).await,
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

    /// `GET /api/<repo>/status` — repository summary: state, default branch,
    /// last-push time, and size counters.
    ///
    /// `state` is `EMPTY` (never pushed) or `READY` today. Once the migration
    /// importer (`docs/large-repo-migration.md`) exists, an in-progress import
    /// reports `MIGRATING` here with progress fields; the shape is designed to
    /// carry that without breaking existing consumers.
    async fn api_status(&self, repo: &Repo<'_>) -> Response {
        let (state, version) = match repo.load_state().await {
            Ok(s) => s,
            Err(e) => return Response::error(500, &e),
        };
        let empty = state.packs.is_empty() && state.refs.is_empty();
        // Default branch: HEAD's symref target with the refs/heads/ prefix
        // stripped, when it points at a local branch.
        let default_branch = state
            .head
            .strip_prefix("refs/heads/")
            .map(|s| s.to_string());
        let objects: u64 = state.packs.iter().map(|p| p.objects).sum();
        let bytes: u64 = state.packs.iter().map(|p| p.bytes).sum();
        Response::json(
            200,
            json!({
                "status": if empty { "EMPTY" } else { "READY" },
                "head": state.head,
                "default_branch": default_branch,
                "head_commit": state.head_oid(),
                "last_push_ms": state.last_push_ms,
                "refs": state.refs.len(),
                "packs": state.packs.len(),
                "objects": objects,
                "bytes": bytes,
                "version": version,
            }),
        )
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
                let segments =
                    match crate::repo::load_filelog_scoped(repo.store, repo.name, &state, &scope)
                        .await
                    {
                        Ok(s) => s,
                        Err(e) => return Response::error(500, &e),
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
                let segments =
                    match crate::repo::load_filelog_scoped(repo.store, repo.name, &state, &scope)
                        .await
                    {
                        Ok(s) => s,
                        Err(e) => return Response::error(500, &e),
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
        let (state, _) = repo
            .load_state()
            .await
            .map_err(|e| Response::error(500, &e))?;
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

/// Stream a shared buffer as 1 MiB chunks (each chunk is a transient copy;
/// the buffer itself stays resident exactly once).
fn chunk_shared(
    data: std::rc::Rc<Vec<u8>>,
) -> futures::stream::LocalBoxStream<'static, Result<Vec<u8>, String>> {
    use futures::StreamExt;
    let len = data.len();
    futures::stream::iter((0..len).step_by(1024 * 1024).collect::<Vec<_>>())
        .map(move |start| {
            let end = (start + 1024 * 1024).min(data.len());
            Ok(data[start..end].to_vec())
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
