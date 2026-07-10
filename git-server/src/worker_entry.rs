//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! Thin glue between the Workers runtime and the transport-agnostic crate:
//!
//! * [`R2Store`] — implements [`crate::storage::Store`] over an R2 bucket,
//!   including streaming multipart uploads (5 MiB part buffering) so pushed
//!   packs flow to R2 without ever being resident in the isolate;
//! * [`DoStateStore`] — implements [`crate::refs::StateStore`] by calling the
//!   per-repo `RepoStateDo` Durable Object, the repo's single serialization
//!   point (load / compare-and-swap commit over a tiny JSON protocol);
//! * `#[event(fetch)]` — adapts the Workers request (streamed body) to
//!   [`crate::http::GitHttp`];
//! * `#[event(scheduled)]` — walks the repo registry (a KV namespace,
//!   updated on push) and runs pack consolidation on repos that need it.

use crate::http::{GitHttp, Request as HttpRequest};
use crate::protocol::BodyStream;
use crate::refs::{RepoState, StateError, StateStore};
use crate::storage::{Result as StorageResult, StorageError, Store, Uploader};
use async_trait::async_trait;
use futures::StreamExt;
use serde::{Deserialize, Serialize};
use worker::{
    durable_object, event, Bucket, Context, Env, Method, MultipartUpload, Range, Request,
    RequestInit, Response, State, UploadedPart,
};

const BUCKET_BINDING: &str = "GIT_BUCKET";
const DO_BINDING: &str = "REPO_STATE";
const REPOS_KV_BINDING: &str = "GIT_REPOS";

/// R2 requires all parts except the last to be at least 5 MiB.
const PART_SIZE: usize = 5 * 1024 * 1024;

fn s_err<E: std::fmt::Display>(e: E) -> StorageError {
    StorageError(e.to_string())
}

// ---------------------------------------------------------------------------
// R2-backed Store
// ---------------------------------------------------------------------------

pub struct R2Store {
    bucket: Bucket,
}

impl R2Store {
    pub fn new(env: &Env) -> worker::Result<Self> {
        Ok(R2Store {
            bucket: env.bucket(BUCKET_BINDING)?,
        })
    }
}

#[async_trait(?Send)]
impl Store for R2Store {
    async fn put(&self, key: &str, data: Vec<u8>) -> StorageResult<()> {
        self.bucket.put(key, data).execute().await.map_err(s_err)?;
        Ok(())
    }

    async fn get(&self, key: &str) -> StorageResult<Option<Vec<u8>>> {
        match self.bucket.get(key).execute().await.map_err(s_err)? {
            Some(obj) => match obj.body() {
                Some(body) => Ok(Some(body.bytes().await.map_err(s_err)?)),
                None => Ok(Some(Vec::new())),
            },
            None => Ok(None),
        }
    }

    async fn get_range(&self, key: &str, offset: u64, len: u64) -> StorageResult<Option<Vec<u8>>> {
        let got = self
            .bucket
            .get(key)
            .range(Range::OffsetWithLength {
                offset,
                length: len,
            })
            .execute()
            .await
            .map_err(s_err)?;
        match got {
            Some(obj) => match obj.body() {
                Some(body) => Ok(Some(body.bytes().await.map_err(s_err)?)),
                None => Ok(Some(Vec::new())),
            },
            None => Ok(None),
        }
    }

    async fn size(&self, key: &str) -> StorageResult<Option<u64>> {
        Ok(self
            .bucket
            .head(key)
            .await
            .map_err(s_err)?
            .map(|o| o.size()))
    }

    async fn delete(&self, key: &str) -> StorageResult<()> {
        self.bucket.delete(key).await.map_err(s_err)
    }

    async fn start_upload(&self, key: &str) -> StorageResult<Box<dyn Uploader>> {
        let upload = self
            .bucket
            .create_multipart_upload(key)
            .execute()
            .await
            .map_err(s_err)?;
        Ok(Box::new(R2Uploader {
            upload,
            parts: Vec::new(),
            buf: Vec::with_capacity(PART_SIZE),
            next_part: 1,
            total: 0,
        }))
    }
}

struct R2Uploader {
    upload: MultipartUpload,
    parts: Vec<UploadedPart>,
    buf: Vec<u8>,
    next_part: u16,
    total: u64,
}

impl R2Uploader {
    async fn flush_part(&mut self) -> StorageResult<()> {
        if self.buf.is_empty() {
            return Ok(());
        }
        let data = std::mem::take(&mut self.buf);
        let part = self
            .upload
            .upload_part(self.next_part, data)
            .await
            .map_err(s_err)?;
        self.parts.push(part);
        self.next_part += 1;
        Ok(())
    }
}

#[async_trait(?Send)]
impl Uploader for R2Uploader {
    async fn write(&mut self, chunk: &[u8]) -> StorageResult<()> {
        self.total += chunk.len() as u64;
        self.buf.extend_from_slice(chunk);
        while self.buf.len() >= PART_SIZE {
            let rest = self.buf.split_off(PART_SIZE);
            let full = std::mem::replace(&mut self.buf, rest);
            let part = self
                .upload
                .upload_part(self.next_part, full)
                .await
                .map_err(s_err)?;
            self.parts.push(part);
            self.next_part += 1;
        }
        Ok(())
    }

    async fn complete(mut self: Box<Self>) -> StorageResult<u64> {
        self.flush_part().await?;
        let parts = std::mem::take(&mut self.parts);
        self.upload.complete(parts).await.map_err(s_err)?;
        Ok(self.total)
    }

    async fn abort(self: Box<Self>) -> StorageResult<()> {
        self.upload.abort().await.map_err(s_err)
    }
}

// ---------------------------------------------------------------------------
// Durable Object: per-repo state
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
struct LoadReply {
    state: RepoState,
    version: u64,
}

#[derive(Serialize, Deserialize)]
struct CommitRequest {
    expected_version: u64,
    state: RepoState,
}

/// The per-repo Durable Object. Every request for a given repo name routes to
/// the same instance, whose single-threaded execution makes `commit` a true
/// compare-and-swap.
#[durable_object]
pub struct RepoStateDo {
    state: State,
}

#[durable_object]
impl DurableObject for RepoStateDo {
    fn new(state: State, _env: Env) -> Self {
        RepoStateDo { state }
    }

    async fn fetch(&mut self, mut req: Request) -> worker::Result<Response> {
        let storage = self.state.storage();
        let version: u64 = storage.get("version").await.unwrap_or(0);
        match req.path().as_str() {
            "/load" => {
                let state: RepoState = storage
                    .get("state")
                    .await
                    .unwrap_or_else(|_| RepoState::empty());
                Response::from_json(&LoadReply { state, version })
            }
            "/commit" => {
                let body: CommitRequest = req.json().await?;
                if body.expected_version != version {
                    return Response::error("conflict", 409);
                }
                let next = version + 1;
                self.state.storage().put("state", &body.state).await?;
                self.state.storage().put("version", next).await?;
                Response::from_json(&serde_json::json!({ "version": next }))
            }
            _ => Response::error("not found", 404),
        }
    }
}

/// [`StateStore`] client speaking to the Durable Object.
pub struct DoStateStore {
    env: Env,
}

impl DoStateStore {
    async fn call(
        &self,
        repo: &str,
        path: &str,
        body: Option<String>,
    ) -> Result<Response, StateError> {
        let ns = self
            .env
            .durable_object(DO_BINDING)
            .map_err(|e| StateError::Backend(e.to_string()))?;
        let stub = ns
            .id_from_name(repo)
            .and_then(|id| id.get_stub())
            .map_err(|e| StateError::Backend(e.to_string()))?;
        let mut init = RequestInit::new();
        init.with_method(if body.is_some() {
            Method::Post
        } else {
            Method::Get
        });
        if let Some(b) = body {
            init.with_body(Some(b.into()));
        }
        let req = Request::new_with_init(&format!("https://do{path}"), &init)
            .map_err(|e| StateError::Backend(e.to_string()))?;
        stub.fetch_with_request(req)
            .await
            .map_err(|e| StateError::Backend(e.to_string()))
    }
}

#[async_trait(?Send)]
impl StateStore for DoStateStore {
    async fn load(&self, repo: &str) -> Result<(RepoState, u64), StateError> {
        let mut resp = self.call(repo, "/load", None).await?;
        let reply: LoadReply = resp
            .json()
            .await
            .map_err(|e| StateError::Backend(e.to_string()))?;
        Ok((reply.state, reply.version))
    }

    async fn commit(
        &self,
        repo: &str,
        expected_version: u64,
        state: &RepoState,
    ) -> Result<u64, StateError> {
        let body = serde_json::to_string(&CommitRequest {
            expected_version,
            state: state.clone(),
        })
        .map_err(|e| StateError::Backend(e.to_string()))?;
        let mut resp = self.call(repo, "/commit", Some(body)).await?;
        if resp.status_code() == 409 {
            return Err(StateError::Conflict);
        }
        if resp.status_code() != 200 {
            return Err(StateError::Backend(format!(
                "commit failed with status {}",
                resp.status_code()
            )));
        }
        let value: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| StateError::Backend(e.to_string()))?;
        Ok(value["version"].as_u64().unwrap_or(0))
    }
}

// ---------------------------------------------------------------------------
// Request body streaming
// ---------------------------------------------------------------------------

struct WorkerBody {
    stream: Option<worker::ByteStream>,
}

#[async_trait(?Send)]
impl BodyStream for WorkerBody {
    async fn next_chunk(&mut self) -> Result<Option<Vec<u8>>, String> {
        match &mut self.stream {
            Some(s) => match s.next().await {
                Some(Ok(chunk)) => Ok(Some(chunk)),
                Some(Err(e)) => Err(e.to_string()),
                None => Ok(None),
            },
            None => Ok(None),
        }
    }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

/// Per-request nonce for staged pack keys: time plus JS randomness.
fn request_nonce() -> String {
    let ms = worker::Date::now().as_millis();
    let r = (worker::js_sys::Math::random() * 1e9) as u64;
    format!("{ms:x}-{r:x}")
}

#[event(fetch)]
async fn fetch(mut req: Request, env: Env, _ctx: Context) -> worker::Result<Response> {
    let store = R2Store::new(&env)?;
    let states = DoStateStore { env: env.clone() };
    let server = GitHttp {
        store: &store,
        states: &states,
    };

    let url = req.url()?;
    let path = url.path().to_string();
    let query = url.query().map(|q| q.to_string());
    let method = req.method().to_string();
    let git_protocol = req.headers().get("Git-Protocol").ok().flatten();
    let content_encoding = req.headers().get("Content-Encoding").ok().flatten();

    let http_req = HttpRequest {
        method: &method,
        path: &path,
        query: query.as_deref(),
        git_protocol: git_protocol.as_deref(),
        content_encoding: content_encoding.as_deref(),
    };
    let mut body = WorkerBody {
        stream: req.stream().ok(),
    };

    let nonce = request_nonce();
    let resp = server.handle(&http_req, &mut body, &nonce).await;

    // Register the repo for scheduled maintenance after a successful push.
    // Read-before-write: a KV read is ~10x cheaper than a write, and every
    // push after the first hits the read path.
    if method == "POST" && path.ends_with("/git-receive-pack") && resp.status == 200 {
        if let Some(repo) = path
            .trim_matches('/')
            .split('/')
            .next()
            .map(|r| r.trim_end_matches(".git"))
        {
            if let Ok(kv) = env.kv(REPOS_KV_BINDING) {
                let known = kv.get(repo).text().await.ok().flatten().is_some();
                if !known {
                    if let Ok(put) = kv.put(repo, "1") {
                        let _ = put.execute().await;
                    }
                }
            }
        }
    }

    let mut headers = worker::Headers::new();
    headers.set("Content-Type", &resp.content_type)?;
    headers.set("Cache-Control", "no-cache")?;
    Ok(Response::from_bytes(resp.body)?
        .with_status(resp.status)
        .with_headers(headers))
}

/// Scheduled maintenance: repack every registered repo that has accumulated
/// multiple packs. Runs are cheap when there is nothing to do (one DO read
/// per repo).
#[event(scheduled)]
async fn scheduled(_event: worker::ScheduledEvent, env: Env, _ctx: worker::ScheduleContext) {
    let store = match R2Store::new(&env) {
        Ok(s) => s,
        Err(e) => {
            worker::console_error!("scheduled: no bucket: {e}");
            return;
        }
    };
    let states = DoStateStore { env: env.clone() };
    let kv = match env.kv(REPOS_KV_BINDING) {
        Ok(kv) => kv,
        Err(e) => {
            worker::console_error!("scheduled: no repo registry: {e}");
            return;
        }
    };
    let repos = match kv.list().execute().await {
        Ok(list) => list.keys,
        Err(e) => {
            worker::console_error!("scheduled: list failed: {e}");
            return;
        }
    };
    for key in repos {
        let repo = crate::repo::Repo {
            store: &store,
            states: &states,
            name: &key.name,
        };
        match crate::maintenance::repack(&repo, &request_nonce()).await {
            Ok(outcome) => {
                worker::console_log!("repack {}: {:?}", key.name, outcome)
            }
            Err(e) => worker::console_error!("repack {} failed: {e}", key.name),
        }
    }
}
