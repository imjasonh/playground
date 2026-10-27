//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! Thin glue between the Workers runtime and the transport-agnostic crate:
//!
//! * [`R2Store`] — implements [`crate::storage::Store`] over an R2 bucket,
//!   including streaming multipart uploads (5 MiB part buffering) so pushed
//!   packs flow to R2 without ever being resident in the isolate;
//! * [`DoStateStore`] — implements [`crate::refs::StateStore`] by calling the
//!   per-repo `RepoStateDo` Durable Object, the repo's single serialization
//!   point (load, per-push merge-apply, and the repack manifest swap, over a
//!   tiny JSON protocol);
//! * `#[event(fetch)]` — adapts the Workers request (streamed body) to
//!   [`crate::http::GitHttp`];
//! * `#[event(scheduled)]` — walks the repo registry (a KV namespace,
//!   updated on push) and runs pack consolidation on repos that need it.

use crate::http::{GitHttp, Request as HttpRequest};
use crate::metrics::{BackendTimer, Op};
use crate::protocol::BodyStream;
use crate::refs::{
    LoadResult, PushApplied, PushDelta, RepackSwap, RepoState, StateError, StateStore,
};
use crate::storage::{retry_transient, Result as StorageResult, StorageError, Store, Uploader};
use async_trait::async_trait;
use futures::StreamExt;
use serde::{Deserialize, Serialize};
use worker::{
    durable_object, event, Bucket, Context, DurableObject, Env, Method, MultipartUpload, Range,
    Request, RequestInit, Response, State, UploadedPart,
};

const BUCKET_BINDING: &str = "GIT_BUCKET";
const DO_BINDING: &str = "REPO_STATE";
const REPOS_KV_BINDING: &str = "GIT_REPOS";

/// R2 requires all parts except the last to be at least 5 MiB.
const PART_SIZE: usize = 5 * 1024 * 1024;

fn s_err<E: std::fmt::Display>(e: E) -> StorageError {
    StorageError(e.to_string())
}

/// Materialize an R2 object body (shared by `get` / `get_range`): a present
/// object with no body reads as empty bytes.
async fn object_bytes(got: Option<worker::Object>) -> StorageResult<Option<Vec<u8>>> {
    match got {
        Some(obj) => match obj.body() {
            Some(body) => Ok(Some(body.bytes().await.map_err(s_err)?)),
            None => Ok(Some(Vec::new())),
        },
        None => Ok(None),
    }
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
        retry_transient(async || {
            let _t = BackendTimer::start(Op::R2ClassA);
            self.bucket
                .put(key, data.clone())
                .execute()
                .await
                .map_err(s_err)?;
            Ok(())
        })
        .await
    }

    async fn get(&self, key: &str) -> StorageResult<Option<Vec<u8>>> {
        retry_transient(async || {
            let _t = BackendTimer::start(Op::R2ClassB);
            let got = self.bucket.get(key).execute().await.map_err(s_err)?;
            object_bytes(got).await
        })
        .await
    }

    async fn get_range(&self, key: &str, offset: u64, len: u64) -> StorageResult<Option<Vec<u8>>> {
        retry_transient(async || {
            let _t = BackendTimer::start(Op::R2ClassB);
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
            object_bytes(got).await
        })
        .await
    }

    async fn size(&self, key: &str) -> StorageResult<Option<u64>> {
        retry_transient(async || {
            let _t = BackendTimer::start(Op::R2ClassB);
            self.bucket
                .head(key)
                .await
                .map_err(s_err)
                .map(|o| o.map(|obj| obj.size()))
        })
        .await
    }

    async fn delete(&self, key: &str) -> StorageResult<()> {
        retry_transient(async || {
            let _t = BackendTimer::start(Op::R2ClassA);
            self.bucket.delete(key).await.map_err(s_err)
        })
        .await
    }

    async fn start_upload(&self, key: &str) -> StorageResult<Box<dyn Uploader>> {
        let upload = retry_transient(async || {
            let _t = BackendTimer::start(Op::R2ClassA);
            self.bucket
                .create_multipart_upload(key)
                .execute()
                .await
                .map_err(s_err)
        })
        .await?;
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
    /// Upload one part (the only place part numbers advance).
    async fn upload_part(&mut self, data: Vec<u8>) -> StorageResult<()> {
        let part_number = self.next_part;
        // `upload_part` takes the buffer by value, so keep a copy until the
        // call succeeds. A transient failure retries the same part number.
        let part = retry_transient(async || {
            let _t = BackendTimer::start(Op::R2ClassA);
            self.upload
                .upload_part(part_number, data.clone())
                .await
                .map_err(s_err)
        })
        .await?;
        self.parts.push(part);
        self.next_part += 1;
        Ok(())
    }

    async fn flush_part(&mut self) -> StorageResult<()> {
        if self.buf.is_empty() {
            return Ok(());
        }
        let data = std::mem::take(&mut self.buf);
        self.upload_part(data).await
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
            self.upload_part(full).await?;
        }
        Ok(())
    }

    async fn complete(mut self: Box<Self>) -> StorageResult<u64> {
        self.flush_part().await?;
        let parts = std::mem::take(&mut self.parts);
        // `complete` takes the upload by value, so a failed attempt cannot
        // be repeated.
        let _t = BackendTimer::start(Op::R2ClassA);
        self.upload.complete(parts).await.map_err(s_err)?;
        Ok(self.total)
    }

    async fn abort(self: Box<Self>) -> StorageResult<()> {
        retry_transient(async || {
            let _t = BackendTimer::start(Op::R2ClassA);
            self.upload.abort().await.map_err(s_err)
        })
        .await
    }
}

// ---------------------------------------------------------------------------
// Durable Object: per-repo state
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
struct LoadReply {
    state: RepoState,
    version: u64,
    /// Absolute epoch ms when the maintenance lease expires; 0 if free.
    #[serde(default)]
    lease_until_ms: i64,
}

#[derive(Serialize, Deserialize)]
struct LeaseRequest {
    now_ms: i64,
    ttl_ms: i64,
}

/// The per-repo Durable Object. Every request for a given repo name routes to
/// the same instance, whose single-threaded execution makes each merge-apply
/// endpoint (`/apply-push`, `/swap`) an atomic read-merge-write.
#[durable_object]
pub struct RepoStateDo {
    state: State,
    env: Env,
}

impl RepoStateDo {
    fn repack_trigger(&self) -> usize {
        self.env
            .var("REPACK_TRIGGER_PACKS")
            .ok()
            .and_then(|v| v.to_string().trim().parse::<usize>().ok())
            .unwrap_or(crate::maintenance::AUTO_REPACK_TRIGGER_PACKS)
    }

    async fn load_doc(&self) -> worker::Result<LoadResult> {
        let storage = self.state.storage();
        let version: u64 = storage.get("version").await?.unwrap_or(0);
        let state: RepoState = storage.get("state").await?.unwrap_or_else(RepoState::empty);
        let lease_until_ms: i64 = storage.get("lease_until").await?.unwrap_or(0);
        Ok(LoadResult {
            state,
            version,
            lease_until_ms,
        })
    }

    async fn apply_doc(&self, delta: &PushDelta) -> worker::Result<PushApplied> {
        let storage = self.state.storage();
        let version: u64 = storage.get("version").await?.unwrap_or(0);
        let mut state: RepoState = storage.get("state").await?.unwrap_or_else(RepoState::empty);
        let applied = state.merge_push(delta);
        if applied.applied {
            storage.put("state", &state).await?;
            storage.put("version", version + 1).await?;
        }
        Ok(applied)
    }

    async fn swap_doc(&self, swap: &RepackSwap) -> worker::Result<bool> {
        let storage = self.state.storage();
        let version: u64 = storage.get("version").await?.unwrap_or(0);
        let mut state: RepoState = storage.get("state").await?.unwrap_or_else(RepoState::empty);
        let applied = state.merge_repack(swap);
        if applied {
            storage.put("state", &state).await?;
            storage.put("version", version + 1).await?;
        }
        Ok(applied)
    }

    async fn lease_doc(&self, now_ms: i64, ttl_ms: i64) -> worker::Result<bool> {
        let storage = self.state.storage();
        let until: i64 = storage.get("lease_until").await?.unwrap_or(0);
        if until > now_ms {
            return Ok(false);
        }
        storage.put("lease_until", now_ms + ttl_ms).await?;
        Ok(true)
    }

    async fn unlease_doc(&self) -> worker::Result<()> {
        self.state.storage().put("lease_until", 0i64).await?;
        Ok(())
    }

    /// Schedule one repack alarm when this push left the repo at the trigger
    /// and no alarm is waiting. A later push does not move an alarm that is
    /// already set.
    async fn arm_repack_alarm(&self) -> worker::Result<()> {
        let trigger = self.repack_trigger();
        let storage = self.state.storage();
        let state: RepoState = storage.get("state").await?.unwrap_or_else(RepoState::empty);
        let alarm_set = storage.get_alarm().await?.is_some();
        if !crate::maintenance::should_arm_repack(state.packs.len(), trigger, alarm_set) {
            return Ok(());
        }
        storage.set_alarm(0i64).await
    }

    async fn run_alarm(&self) -> worker::Result<Response> {
        let trigger = self.repack_trigger();
        if trigger == 0 {
            return Response::from_json(&serde_json::json!({
                "evt": "repack_alarm",
                "skipped": "disabled",
            }));
        }
        let Some(repo_name) = self.state.id().name() else {
            worker::console_error!("repack alarm: durable object has no name");
            return Response::from_json(&serde_json::json!({
                "evt": "repack_alarm",
                "skipped": "unnamed",
            }));
        };
        let store = R2Store::new(&self.env)?;
        // The repack borrows this object through `DirectState`. Schedule the
        // next alarm after that borrow ends. Storage and the repack cannot
        // both hold `self`.
        let step = {
            let states = DirectState { owner: self };
            let repo = crate::repo::Repo {
                store: &store,
                states: &states,
                name: &repo_name,
            };
            match repo.load_state().await {
                Err(e) => AlarmStep::LoadFailed(e),
                Ok(loaded) if loaded.state.packs.len() < trigger => {
                    AlarmStep::Skip { packs: loaded.state.packs.len() }
                }
                Ok(loaded) => {
                    let packs = loaded.state.packs.len();
                    crate::metrics::begin();
                    let start = crate::metrics::now_ms();
                    let result = crate::maintenance::repack(&repo, &request_nonce()).await;
                    let _metrics = crate::metrics::take();
                    let ms = crate::metrics::now_ms() - start;
                    match result {
                        Ok(outcome) => {
                            let packs_after = repo
                                .load_state()
                                .await
                                .map(|again| again.state.packs.len())
                                .unwrap_or(packs);
                            AlarmStep::Done {
                                packs,
                                packs_after,
                                outcome,
                                ms,
                            }
                        }
                        Err(error) => AlarmStep::Failed { packs, error, ms },
                    }
                }
            }
        };
        match step {
            AlarmStep::LoadFailed(error) => {
                worker::console_error!("repack alarm {repo_name} load: {error}");
                self.state.storage().set_alarm(5_000i64).await?;
                Response::from_json(&serde_json::json!({
                    "evt": "repack_alarm",
                    "repo": repo_name,
                    "error": error,
                }))
            }
            AlarmStep::Skip { packs } => Response::from_json(&serde_json::json!({
                "evt": "repack_alarm",
                "repo": repo_name,
                "packs": packs,
                "skipped": "under trigger",
            })),
            AlarmStep::Failed { packs, error, ms } => {
                worker::console_error!("repack alarm {repo_name} failed: {error}");
                self.state.storage().set_alarm(5_000i64).await?;
                Response::from_json(&serde_json::json!({
                    "evt": "repack_alarm",
                    "repo": repo_name,
                    "packs": packs,
                    "error": error,
                    "ms": ms,
                }))
            }
            AlarmStep::Done {
                packs,
                packs_after,
                outcome,
                ms,
            } => {
                if let Some(delay) =
                    crate::maintenance::repack_followup_delay_ms(&outcome, packs_after, trigger)
                {
                    self.state.storage().set_alarm(delay).await?;
                }
                let body = serde_json::json!({
                    "evt": "repack_alarm",
                    "repo": repo_name,
                    "packs": packs,
                    "packs_after": packs_after,
                    "outcome": format!("{outcome:?}"),
                    "ms": ms,
                });
                worker::console_log!("{}", body);
                Response::from_json(&body)
            }
        }
    }
}

enum AlarmStep {
    LoadFailed(String),
    Skip { packs: usize },
    Failed { packs: usize, error: String, ms: f64 },
    Done {
        packs: usize,
        packs_after: usize,
        outcome: crate::maintenance::RepackOutcome,
        ms: f64,
    },
}

/// [`StateStore`] backed by this Durable Object's own storage.
///
/// The alarm runs inside the object, so it cannot `fetch` its own stub.
/// That call would wait for the alarm to finish.
struct DirectState<'a> {
    owner: &'a RepoStateDo,
}

fn state_err(err: worker::Error) -> StateError {
    StateError::Backend(err.to_string())
}

#[async_trait(?Send)]
impl StateStore for DirectState<'_> {
    async fn load(&self, _repo: &str) -> Result<LoadResult, StateError> {
        self.owner.load_doc().await.map_err(state_err)
    }

    async fn apply_push(&self, _repo: &str, delta: &PushDelta) -> Result<PushApplied, StateError> {
        self.owner.apply_doc(delta).await.map_err(state_err)
    }

    async fn apply_repack(&self, _repo: &str, swap: &RepackSwap) -> Result<bool, StateError> {
        self.owner.swap_doc(swap).await.map_err(state_err)
    }

    async fn repack_lease(&self, _repo: &str, now_ms: i64, ttl_ms: i64) -> Result<bool, StateError> {
        self.owner.lease_doc(now_ms, ttl_ms).await.map_err(state_err)
    }

    async fn repack_unlease(&self, _repo: &str) -> Result<(), StateError> {
        self.owner.unlease_doc().await.map_err(state_err)
    }
}

impl DurableObject for RepoStateDo {
    fn new(state: State, env: Env) -> Self {
        RepoStateDo { state, env }
    }

    // worker >= 0.6: DO handlers take `&self` (storage is interior-mutable).
    // worker >= 0.7: `storage.get` returns `Result<Option<T>>` (missing key is
    // `Ok(None)`, not an error).
    async fn fetch(&self, mut req: Request) -> worker::Result<Response> {
        match req.path().as_str() {
            "/load" => {
                let loaded = self.load_doc().await?;
                Response::from_json(&LoadReply {
                    state: loaded.state,
                    version: loaded.version,
                    lease_until_ms: loaded.lease_until_ms,
                })
            }
            // Merge-apply one push's delta against the current state
            // (per-ref CAS + commuting appends). Single-threaded execution
            // plus the storage input gate make read-merge-write atomic, so
            // concurrent pushes to disjoint refs all land. Bumps the
            // monotonic state version surfaced by the status API.
            // A push that crosses the repack trigger arms an alarm. The
            // alarm runs outside this request, so a crashed push cannot
            // leave the maintenance lease held.
            "/apply" => {
                let delta: PushDelta = req.json().await?;
                let applied = self.apply_doc(&delta).await?;
                if applied.applied {
                    if let Err(err) = self.arm_repack_alarm().await {
                        worker::console_error!("arm repack alarm: {err}");
                    }
                }
                Response::from_json(&applied)
            }
            // Repack's manifest swap: replace consumed pack/file-log ids
            // with the consolidated ones, in place. Commutes with racing
            // pushes (they only append); fails only if another repack
            // consumed one of the same ids first.
            "/swap" => {
                let swap: RepackSwap = req.json().await?;
                let applied = self.swap_doc(&swap).await?;
                Response::from_json(&serde_json::json!({ "applied": applied }))
            }
            // Maintenance lease: collapses concurrent repack triggers
            // (the alarm, cron, on-demand API) to one holder.
            // Single-threaded DO execution makes test-and-set atomic; the
            // TTL bounds a crashed holder.
            "/lease" => {
                let body: LeaseRequest = req.json().await?;
                let acquired = self.lease_doc(body.now_ms, body.ttl_ms).await?;
                Response::from_json(&serde_json::json!({ "acquired": acquired }))
            }
            "/unlease" => {
                self.unlease_doc().await?;
                Response::from_json(&serde_json::json!({ "released": true }))
            }
            _ => Response::error("not found", 404),
        }
    }

    async fn alarm(&self) -> worker::Result<Response> {
        crate::scope::run(crate::scope::fresh(), self.run_alarm()).await
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
        let _t = BackendTimer::start(Op::DoRequest);
        stub.fetch_with_request(req)
            .await
            .map_err(|e| StateError::Backend(e.to_string()))
    }
}

#[async_trait(?Send)]
impl StateStore for DoStateStore {
    async fn load(&self, repo: &str) -> Result<LoadResult, StateError> {
        let mut resp = self.call(repo, "/load", None).await?;
        let reply: LoadReply = resp
            .json()
            .await
            .map_err(|e| StateError::Backend(e.to_string()))?;
        Ok(LoadResult {
            state: reply.state,
            version: reply.version,
            lease_until_ms: reply.lease_until_ms,
        })
    }

    async fn apply_push(&self, repo: &str, delta: &PushDelta) -> Result<PushApplied, StateError> {
        let body = serde_json::to_string(delta).map_err(|e| StateError::Backend(e.to_string()))?;
        let mut resp = self.call(repo, "/apply", Some(body)).await?;
        if resp.status_code() != 200 {
            return Err(StateError::Backend(format!(
                "apply failed with status {}",
                resp.status_code()
            )));
        }
        resp.json()
            .await
            .map_err(|e| StateError::Backend(e.to_string()))
    }

    async fn apply_repack(&self, repo: &str, swap: &RepackSwap) -> Result<bool, StateError> {
        let body = serde_json::to_string(swap).map_err(|e| StateError::Backend(e.to_string()))?;
        let mut resp = self.call(repo, "/swap", Some(body)).await?;
        if resp.status_code() != 200 {
            return Err(StateError::Backend(format!(
                "swap failed with status {}",
                resp.status_code()
            )));
        }
        let value: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| StateError::Backend(e.to_string()))?;
        Ok(value["applied"].as_bool().unwrap_or(false))
    }

    async fn repack_lease(&self, repo: &str, now_ms: i64, ttl_ms: i64) -> Result<bool, StateError> {
        let body = serde_json::to_string(&LeaseRequest { now_ms, ttl_ms })
            .map_err(|e| StateError::Backend(e.to_string()))?;
        let mut resp = self.call(repo, "/lease", Some(body)).await?;
        let value: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| StateError::Backend(e.to_string()))?;
        Ok(value["acquired"].as_bool().unwrap_or(false))
    }

    async fn repack_unlease(&self, repo: &str) -> Result<(), StateError> {
        let _ = self.call(repo, "/unlease", Some("{}".into())).await?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Request body streaming
// ---------------------------------------------------------------------------

/// Streams the request body chunk-by-chunk from the Workers runtime.
///
/// Uses `worker::ByteStream` directly: the edge delivers the body in small
/// frames (~4 KiB, confirmed in production via the `max_chunk_in` metric), so
/// each chunk copied into wasm is tiny and there is no whole-body buffering to
/// avoid. (An earlier version hand-drove the JS `ReadableStream` reader and
/// re-sliced every chunk to guard against the edge delivering multi-MB chunks
/// — a scenario the measurements disproved; that guard only added a
/// per-chunk `Reflect` lookup, so it was removed.)
struct WorkerBody {
    stream: Option<worker::ByteStream>,
}

#[async_trait(?Send)]
impl BodyStream for WorkerBody {
    async fn next_chunk(&mut self) -> Result<Option<Vec<u8>>, String> {
        match &mut self.stream {
            Some(s) => match s.next().await {
                Some(Ok(chunk)) => {
                    crate::metrics::add_bytes_in(chunk.len() as u64);
                    Ok(Some(chunk))
                }
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
async fn fetch(req: Request, env: Env, _ctx: Context) -> worker::Result<Response> {
    let mut server = GitHttp::new(
        std::rc::Rc::new(R2Store::new(&env)?),
        std::rc::Rc::new(DoStateStore { env: env.clone() }),
    );
    // Optional override for zones with a higher request-body cap
    // (Business/Enterprise); defaults to the Free/Pro 100 MB limit.
    if let Some(limit) = env
        .var("PUSH_LIMIT_BYTES")
        .ok()
        .and_then(|v| v.to_string().trim().parse::<u64>().ok())
        .filter(|n| *n > 0)
    {
        server = server.with_push_limit(limit);
    }
    let url = req.url()?;
    let path = url.path().to_string();
    let query = url.query().map(|q| q.to_string());
    let method = req.method().to_string();
    let git_protocol = req.headers().get("Git-Protocol").ok().flatten();
    let content_encoding = req.headers().get("Content-Encoding").ok().flatten();
    let cf_ray = req.headers().get("cf-ray").ok().flatten();

    let span_name = if path.contains("git-receive-pack") {
        "git.receive_pack"
    } else if path.contains("git-upload-pack") {
        "git.upload_pack"
    } else if path.starts_with("/api/") {
        "git.api"
    } else {
        "git.handle"
    };

    let method_for_span = method.clone();
    let path_for_span = path.clone();
    let ray_for_span = cf_ray.clone();

    let span = crate::trace::span_async(span_name, move |span| async move {
        if span.is_traced() {
            span.set_attribute("http.request.method", &method_for_span);
            span.set_attribute("url.path", &path_for_span);
            if let Some(ref r) = ray_for_span {
                span.set_attribute("cloudflare.ray_id", r);
            }
        }
        fetch_inner(FetchCtx {
            req,
            env,
            server,
            method,
            path,
            query,
            git_protocol,
            content_encoding,
            cf_ray,
        })
        .await
    });
    crate::scope::run(crate::scope::fresh(), span).await
}

struct FetchCtx {
    req: Request,
    env: Env,
    server: GitHttp,
    method: String,
    path: String,
    query: Option<String>,
    git_protocol: Option<String>,
    content_encoding: Option<String>,
    cf_ray: Option<String>,
}

async fn fetch_inner(ctx: FetchCtx) -> worker::Result<Response> {
    let FetchCtx {
        mut req,
        env,
        server,
        method,
        path,
        query,
        git_protocol,
        content_encoding,
        cf_ray,
    } = ctx;

    let mut body = WorkerBody {
        stream: req.stream().ok(),
    };

    let http_req = HttpRequest {
        method: &method,
        path: &path,
        query: query.as_deref(),
        git_protocol: git_protocol.as_deref(),
        content_encoding: content_encoding.as_deref(),
        cf_ray: cf_ray.as_deref(),
    };

    let nonce = request_nonce();
    let mut resp = server.handle(&http_req, &mut body, &nonce).await;

    // Register the repo for scheduled maintenance after a successful push.
    // Read-before-write: a KV read is ~10x cheaper than a write, and every
    // push after the first hits the read path. (This runs after the metrics
    // collector was drained, so account for it directly.)
    if method == "POST" && path.ends_with("/git-receive-pack") && resp.status == 200 {
        if let Some(repo) = path
            .trim_matches('/')
            .split('/')
            .next()
            .map(|r| r.trim_end_matches(".git"))
        {
            if let Ok(kv) = env.kv(REPOS_KV_BINDING) {
                let kv_start = crate::metrics::now_ms();
                let known = kv.get(repo).text().await.ok().flatten().is_some();
                let mut kv_ops = 1;
                if !known {
                    if let Ok(put) = kv.put(repo, "1") {
                        let _ = put.execute().await;
                        kv_ops += 1;
                    }
                }
                if let Some((m, _)) = resp.metrics.as_deref_mut() {
                    m.kv_ops += kv_ops;
                    m.backend_ms += crate::metrics::now_ms() - kv_start;
                }
            }
        }
    }

    // Emit observability: a Server-Timing header (curl / browser visible)
    // and one structured JSON log line per request (Workers Logs /
    // `wrangler tail`) carrying the cost-model op counts and phase timings.
    let headers = worker::Headers::new();
    headers.set("Content-Type", &resp.content_type)?;
    headers.set("Cache-Control", "no-cache")?;
    if let Some(header) = resp.server_timing() {
        headers.set("Server-Timing", &header)?;
    }
    if let Some((m, total_ms)) = resp.metrics.as_deref() {
        worker::console_log!("{}", m.log_json(&method, &path, resp.status, *total_ms));
    }
    // Full bodies relay directly; streamed bodies (fetch packs, large blobs)
    // flow chunk-by-chunk through a ReadableStream so a response of any size
    // fits the isolate memory limit.
    let out = match resp.body {
        crate::http::Body::Full(bytes) => Response::from_bytes(bytes)?,
        crate::http::Body::Stream(stream) => {
            use futures::TryStreamExt;
            Response::from_stream(stream.map_err(worker::Error::RustError))?
        }
    };
    Ok(out.with_status(resp.status).with_headers(headers))
}

/// Scheduled maintenance: repack every registered repo that has accumulated
/// multiple packs. Runs are cheap when there is nothing to do (one DO read
/// per repo).
#[event(scheduled)]
async fn scheduled(_event: worker::ScheduledEvent, env: Env, _ctx: worker::ScheduleContext) {
    let run = crate::trace::span_async("git.scheduled", move |_span| async move {
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
            crate::trace::with_active_span(|span| {
                if span.is_traced() {
                    span.set_attribute("git.repo", &key.name);
                }
            });
            let repo = crate::repo::Repo {
                store: &store,
                states: &states,
                name: &key.name,
            };
            crate::metrics::begin();
            let start = crate::metrics::now_ms();
            let result = crate::maintenance::repack(&repo, &request_nonce()).await;
            let total_ms = crate::metrics::now_ms() - start;
            let metrics = crate::metrics::take();
            match result {
                Ok(outcome) => {
                    worker::console_log!("repack {}: {:?}", key.name, outcome);
                    if let Some(m) = metrics {
                        worker::console_log!(
                            "{}",
                            m.log_json("CRON", &format!("/repack/{}", key.name), 200, total_ms)
                        );
                    }
                }
                Err(e) => worker::console_error!("repack {} failed: {e}", key.name),
            }
        }
    });
    crate::scope::run(crate::scope::fresh(), run).await;
}
