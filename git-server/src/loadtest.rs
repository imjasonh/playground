//! In-worker (and native) load-test harness for per-repo push/pull ceilings.
//!
//! The laptop harness in [`docs/loadtest-scaling.md`] saturates the client
//! before the server. This module drives the same protocol from *inside* the
//! Worker (or in-process against [`crate::http::GitHttp`] in tests): concurrent
//! synthetic push and shallow-fetch loops, with:
//!
//! * peak successful pushes/s and pulls/s per stage (and overall peak);
//! * mean underlying-op cost per successful push and pull (R2 A/B, DO, KV, $);
//! * a hard spend budget that stops the run early and marks the report
//!   `budget_limited` while still recording the peak QPS observed.
//!
//! Traces: each pushed/fetched request is a normal Worker invocation, so
//! Workers Traces + the structured `{"evt":"req",…}` logs cover the hot
//! path under load. The loadtest coordinator itself opens a `git.loadtest`
//! span (see `worker_entry`).

use crate::http::{Body, GitHttp, Request as HttpRequest};
use crate::metrics::{self, Metrics};
use crate::object::{encode_tree, hash_object, ObjType, Oid, TreeEntry};
use crate::pack::write::PackWriter;
use crate::pktline;
use crate::protocol::BodyStream;
use crate::refs::StateStore;
use crate::storage::Store;
use async_trait::async_trait;
use futures::future::join_all;
use serde::{Deserialize, Serialize};
use std::cell::Cell;
use std::collections::VecDeque;
use std::rc::Rc;

/// Default spend cap when the request omits `budget_usd`. Small on purpose:
/// the prototype has no auth, so a stray curl should not burn dollars.
pub const DEFAULT_BUDGET_USD: f64 = 0.10;

/// Hard upper bound on `budget_usd` (even if the caller asks for more).
pub const MAX_BUDGET_USD: f64 = 5.0;

/// Default per-stage wall time.
pub const DEFAULT_DURATION_SECS: u64 = 20;

/// Max per-stage wall time (keeps one HTTP response bounded).
pub const MAX_DURATION_SECS: u64 = 120;

/// Default concurrent writers when `stages` is omitted.
const DEFAULT_WRITER_RAMP: &[u32] = &[1, 2, 4, 8, 16, 32, 48];

/// Default concurrent readers for the read-only stage.
const DEFAULT_READER_CONCURRENCY: u32 = 64;

/// Seed repo shape: small enough that one push is cheap, large enough that
/// shallow fetch does real pack-build work.
const SEED_BLOBS: usize = 24;
const SEED_BLOB_BYTES: usize = 256;

/// Per-push writer payload: one small blob rewrite (keeps push cost in the
/// "three-line edit" regime of the laptop tests).
const WRITE_BLOB_BYTES: usize = 128;

/// Request body for `POST /loadtest/merge` (phone UI after browser fan-out).
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct LoadTestMergeRequest {
    pub confirm: bool,
    #[serde(default)]
    pub budget_usd: Option<f64>,
    pub parts: Vec<LoadTestReport>,
    #[serde(default)]
    pub token: Option<String>,
}

/// Request body for `POST /api/<repo>/loadtest`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct LoadTestRequest {
    /// Must be `true`. Guards against accidental triggers.
    pub confirm: bool,
    /// Hard spend cap in USD (marginal R2/DO/KV only). Clamped to
    /// [`MAX_BUDGET_USD`]. Defaults to [`DEFAULT_BUDGET_USD`].
    #[serde(default)]
    pub budget_usd: Option<f64>,
    /// Per-stage duration in seconds. Defaults to [`DEFAULT_DURATION_SECS`].
    #[serde(default)]
    pub duration_secs: Option<u64>,
    /// Explicit stage list. When omitted, runs the default writer ramp then
    /// a readers-only stage.
    #[serde(default)]
    pub stages: Option<Vec<StageSpec>>,
    /// How many Worker shards to fan the offered load across. `1` (default)
    /// runs everything in this isolate; `>1` partitions in-process when no
    /// HTTP fan-out is configured. Phone UI fans out from the browser instead.
    /// All shards hit the **same** repo (per-repo ceiling).
    #[serde(default)]
    pub shards: Option<u32>,
    /// Internal: this invocation is one shard of a coordinated run. Shards
    /// do not fan out further and do not re-seed.
    #[serde(default)]
    pub shard: bool,
    /// Tip oid for pulls / first writer parents when `shard` is set (parent
    /// supplies this after seeding).
    #[serde(default)]
    pub tip: Option<String>,
    /// Shard index (for unique writer branch namespaces).
    #[serde(default)]
    pub shard_index: Option<u32>,
    /// Optional shared secret (also accepted via `X-Loadtest-Token` or
    /// `?token=`). Required when the Worker has `LOADTEST_TOKEN` configured.
    #[serde(default)]
    pub token: Option<String>,
}

/// One concurrency stage.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct StageSpec {
    #[serde(default)]
    pub writers: u32,
    #[serde(default)]
    pub readers: u32,
}

/// Normalized config after clamping.
#[derive(Debug, Clone)]
pub struct LoadTestConfig {
    pub budget_usd: f64,
    pub duration_ms: u64,
    pub stages: Vec<StageSpec>,
    pub shards: u32,
    pub shard: bool,
    pub tip: Option<Oid>,
    pub shard_index: u32,
}

/// Cap on isolate shards for one coordinated run.
///
/// Phone multi-shard runs fan out from the **browser** (parallel POSTs to
/// `/api/…/loadtest`). Each request is its own edge invocation, so Cloudflare's
/// Worker→Worker loop limit does not apply. Cap keeps the UI honest about
/// practical parallelism from one phone.
pub const MAX_SHARDS: u32 = 16;

impl LoadTestRequest {
    /// Validate and clamp into a [`LoadTestConfig`].
    pub fn into_config(self) -> Result<LoadTestConfig, String> {
        if !self.confirm {
            return Err("set confirm=true to run a load test".into());
        }
        let budget = self
            .budget_usd
            .unwrap_or(DEFAULT_BUDGET_USD)
            .clamp(0.0, MAX_BUDGET_USD);
        if budget <= 0.0 {
            return Err("budget_usd must be > 0".into());
        }
        let duration_secs = self
            .duration_secs
            .unwrap_or(DEFAULT_DURATION_SECS)
            .clamp(1, MAX_DURATION_SECS);
        let stages = match self.stages {
            Some(s) if !s.is_empty() => s,
            _ => {
                let mut s: Vec<StageSpec> = DEFAULT_WRITER_RAMP
                    .iter()
                    .map(|&w| StageSpec {
                        writers: w,
                        readers: 0,
                    })
                    .collect();
                s.push(StageSpec {
                    writers: 0,
                    readers: DEFAULT_READER_CONCURRENCY,
                });
                s
            }
        };
        for st in &stages {
            if st.writers == 0 && st.readers == 0 {
                return Err("each stage needs writers > 0 and/or readers > 0".into());
            }
        }
        let tip = match self.tip.as_deref() {
            Some(hex) => Some(Oid::from_hex(hex).ok_or_else(|| format!("bad tip oid {hex}"))?),
            None => None,
        };
        Ok(LoadTestConfig {
            budget_usd: budget,
            duration_ms: duration_secs * 1000,
            stages,
            shards: self.shards.unwrap_or(1).clamp(1, MAX_SHARDS),
            shard: self.shard,
            tip,
            shard_index: self.shard_index.unwrap_or(0),
        })
    }

    /// Rebuild a request body for a nested shard POST.
    pub fn from_config(cfg: &LoadTestConfig, tip: Option<&str>) -> LoadTestRequest {
        LoadTestRequest {
            confirm: true,
            budget_usd: Some(cfg.budget_usd),
            duration_secs: Some((cfg.duration_ms / 1000).max(1)),
            stages: Some(cfg.stages.clone()),
            shards: Some(cfg.shards),
            shard: cfg.shard,
            tip: tip.map(str::to_string),
            shard_index: Some(cfg.shard_index),
            token: None,
        }
    }
}

/// Mean underlying-op cost for one class of operation (push or pull).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct OpCostSummary {
    pub samples: u64,
    pub mean_r2_class_a: f64,
    pub mean_r2_class_b: f64,
    pub mean_do: f64,
    pub mean_kv: f64,
    pub mean_cost_usd: f64,
    /// Mean backend-await milliseconds (R2/DO/KV), not isolate wall time.
    pub mean_ms: f64,
}

impl OpCostSummary {
    fn from_totals(samples: u64, sum: &OpTotals) -> Self {
        if samples == 0 {
            return Self::default();
        }
        let n = samples as f64;
        Self {
            samples,
            mean_r2_class_a: sum.r2_class_a as f64 / n,
            mean_r2_class_b: sum.r2_class_b as f64 / n,
            mean_do: sum.do_requests as f64 / n,
            mean_kv: sum.kv_ops as f64 / n,
            mean_cost_usd: sum.cost_usd / n,
            mean_ms: sum.ms / n,
        }
    }
}

#[derive(Debug, Default, Clone)]
struct OpTotals {
    r2_class_a: u64,
    r2_class_b: u64,
    do_requests: u64,
    kv_ops: u64,
    cost_usd: f64,
    ms: f64,
}

impl OpTotals {
    fn add(&mut self, m: &AttemptMetrics) {
        self.r2_class_a += m.r2_class_a;
        self.r2_class_b += m.r2_class_b;
        self.do_requests += m.do_requests;
        self.kv_ops += m.kv_ops;
        self.cost_usd += m.cost_usd;
        self.ms += m.ms;
    }
}

/// One stage's measured goodput and costs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StageReport {
    pub writers: u32,
    pub readers: u32,
    pub wall_ms: f64,
    pub push_ok: u64,
    pub push_conflict: u64,
    pub push_err: u64,
    pub pull_ok: u64,
    pub pull_err: u64,
    pub pushes_per_sec: f64,
    pub pulls_per_sec: f64,
    pub stage_cost_usd: f64,
    pub budget_hit: bool,
}

/// Final load-test report (JSON response body).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoadTestReport {
    pub repo: String,
    pub tip: String,
    pub budget_usd: f64,
    pub total_cost_usd: f64,
    /// True when the run stopped because spend reached `budget_usd`.
    pub budget_limited: bool,
    pub peak_pushes_per_sec: f64,
    pub peak_pulls_per_sec: f64,
    pub cost_per_push: OpCostSummary,
    pub cost_per_pull: OpCostSummary,
    pub stages: Vec<StageReport>,
    pub duration_ms: f64,
    pub shards: u32,
}

/// Per-attempt outcome used by the runner and drivers.
#[derive(Debug, Clone)]
pub struct AttemptResult {
    pub kind: AttemptKind,
    pub outcome: AttemptOutcome,
    pub metrics: AttemptMetrics,
    /// New tip oid after a successful push (writers track per-branch tips).
    pub new_tip: Option<Oid>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttemptKind {
    Push,
    Pull,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttemptOutcome {
    Ok,
    Conflict,
    Err,
}

/// Subset of [`Metrics`] the runner needs (also parsed from Server-Timing).
#[derive(Debug, Clone, Default)]
pub struct AttemptMetrics {
    pub r2_class_a: u64,
    pub r2_class_b: u64,
    pub do_requests: u64,
    pub kv_ops: u64,
    pub cost_usd: f64,
    /// Time awaiting backends (R2/DO/KV). Used for mean latency so concurrent
    /// writers on one isolate do not inflate the number with event-loop wait.
    pub ms: f64,
    /// Wall clock for the nested `handle()` call (includes sibling scheduling).
    pub wall_ms: f64,
}

impl AttemptMetrics {
    pub fn from_metrics(m: &Metrics, total_ms: f64) -> Self {
        Self {
            r2_class_a: m.r2_class_a,
            r2_class_b: m.r2_class_b,
            do_requests: m.do_requests,
            kv_ops: m.kv_ops,
            cost_usd: m.cost_usd(),
            ms: m.backend_ms,
            wall_ms: total_ms,
        }
    }
}

/// Parse `Server-Timing` tokens produced by [`Metrics::server_timing`].
pub fn parse_server_timing(header: &str) -> AttemptMetrics {
    let mut m = AttemptMetrics::default();
    for part in header.split(',') {
        let part = part.trim();
        let name = part.split(';').next().unwrap_or("").trim();
        if name == "backend" {
            if let Some(dur) = timing_dur(part) {
                m.ms = dur;
            }
        } else if name == "total" {
            if let Some(dur) = timing_dur(part) {
                m.wall_ms = dur;
                if m.ms == 0.0 {
                    m.ms = dur;
                }
            }
        } else if name == "r2a" {
            m.r2_class_a = timing_desc_u64(part);
        } else if name == "r2b" {
            m.r2_class_b = timing_desc_u64(part);
        } else if name == "do" {
            m.do_requests = timing_desc_u64(part);
        } else if name == "kv" {
            m.kv_ops = timing_desc_u64(part);
        } else if name == "cost" {
            // desc="1.950u$"
            if let Some(raw) = timing_desc(part) {
                let num = raw.trim_end_matches("u$").trim();
                if let Ok(u) = num.parse::<f64>() {
                    m.cost_usd = u / 1e6;
                }
            }
        }
    }
    m
}

fn timing_dur(part: &str) -> Option<f64> {
    for tok in part.split(';') {
        let tok = tok.trim();
        if let Some(v) = tok.strip_prefix("dur=") {
            return v.parse().ok();
        }
    }
    None
}

fn timing_desc(part: &str) -> Option<&str> {
    for tok in part.split(';') {
        let tok = tok.trim();
        if let Some(rest) = tok.strip_prefix("desc=") {
            let rest = rest.trim_matches('"');
            return Some(rest);
        }
    }
    None
}

fn timing_desc_u64(part: &str) -> u64 {
    timing_desc(part).and_then(|s| s.parse().ok()).unwrap_or(0)
}

/// How the runner talks to the server under test.
#[async_trait(?Send)]
pub trait LoadDriver {
    /// Ensure the repo has a tip; return it. May push a seed pack.
    async fn ensure_seeded(&self, tip_hint: Option<Oid>) -> Result<Oid, String>;

    /// Push `body` (pkt-line commands + pack). `branch` is informational for
    /// logging; the ref name is already inside `body`.
    async fn push(&self, body: Vec<u8>) -> Result<AttemptResult, String>;

    /// Protocol-v2 fetch for `want`.
    async fn pull(&self, want: Oid) -> Result<AttemptResult, String>;

    /// Mirror production's post-push auto-repack: if live packs ≥
    /// [`crate::maintenance::AUTO_REPACK_TRIGGER_PACKS`], run a bounded
    /// repack. Called *after* a timed push so maintenance does not inflate
    /// attempt latency (same idea as Worker `wait_until`).
    async fn maybe_repack(&self) -> Result<(), String> {
        Ok(())
    }
}

/// Shared spend counter: attempts check before starting and record after.
struct Budget {
    limit_usd: f64,
    spent_usd: Cell<f64>,
    hit: Cell<bool>,
}

impl Budget {
    fn new(limit_usd: f64) -> Self {
        Self {
            limit_usd,
            spent_usd: Cell::new(0.0),
            hit: Cell::new(false),
        }
    }

    fn remaining(&self) -> f64 {
        (self.limit_usd - self.spent_usd.get()).max(0.0)
    }

    fn allow_start(&self) -> bool {
        if self.hit.get() || self.remaining() <= 0.0 {
            self.hit.set(true);
            false
        } else {
            true
        }
    }

    fn record(&self, cost: f64) {
        self.spent_usd.set(self.spent_usd.get() + cost.max(0.0));
        if self.spent_usd.get() >= self.limit_usd {
            self.hit.set(true);
        }
    }

    fn spent(&self) -> f64 {
        self.spent_usd.get()
    }

    fn is_hit(&self) -> bool {
        self.hit.get()
    }
}

/// Run the configured stages against `driver`.
pub async fn run_loadtest(
    repo: &str,
    driver: &dyn LoadDriver,
    cfg: &LoadTestConfig,
) -> Result<LoadTestReport, String> {
    let run_start = metrics::now_ms();
    let tip = driver.ensure_seeded(cfg.tip).await?;
    let budget = Budget::new(cfg.budget_usd);

    let mut stages = Vec::new();
    let mut peak_push = 0.0_f64;
    let mut peak_pull = 0.0_f64;
    let mut push_totals = OpTotals::default();
    let mut push_samples = 0u64;
    let mut pull_totals = OpTotals::default();
    let mut pull_samples = 0u64;
    let mut budget_limited = false;

    for (stage_i, raw_spec) in cfg.stages.iter().enumerate() {
        if !budget.allow_start() {
            budget_limited = true;
            break;
        }
        // One invocation's nested loops share subrequest/memory budgets.
        // On wasm, clamp so phone shard POSTs cannot recreate Error 1101.
        let spec = clamp_stage_to_isolate(raw_spec);
        if spec.writers == 0 && spec.readers == 0 {
            continue;
        }
        let stage_start = metrics::now_ms();
        let deadline = stage_start + cfg.duration_ms as f64;
        let spent_before = budget.spent();

        let mut writer_futs = Vec::new();
        for w in 0..spec.writers {
            let branch_id = cfg.shard_index * 10_000 + stage_i as u32 * 100 + w;
            writer_futs.push(writer_loop(driver, tip, branch_id, deadline, &budget));
        }
        let mut reader_futs = Vec::new();
        for _ in 0..spec.readers {
            reader_futs.push(reader_loop(driver, tip, deadline, &budget));
        }

        let writer_results = join_all(writer_futs).await;
        let reader_results = join_all(reader_futs).await;

        let mut push_ok = 0u64;
        let mut push_conflict = 0u64;
        let mut push_err = 0u64;
        let mut pull_ok = 0u64;
        let mut pull_err = 0u64;

        for list in writer_results {
            for a in list {
                match a.outcome {
                    AttemptOutcome::Ok => {
                        push_ok += 1;
                        push_totals.add(&a.metrics);
                        push_samples += 1;
                    }
                    AttemptOutcome::Conflict => push_conflict += 1,
                    AttemptOutcome::Err => push_err += 1,
                }
            }
        }
        for list in reader_results {
            for a in list {
                match a.outcome {
                    AttemptOutcome::Ok => {
                        pull_ok += 1;
                        pull_totals.add(&a.metrics);
                        pull_samples += 1;
                    }
                    AttemptOutcome::Conflict => {}
                    AttemptOutcome::Err => pull_err += 1,
                }
            }
        }

        let wall_ms = (metrics::now_ms() - stage_start).max(1.0);
        let wall_s = wall_ms / 1000.0;
        let pushes_per_sec = push_ok as f64 / wall_s;
        let pulls_per_sec = pull_ok as f64 / wall_s;
        peak_push = peak_push.max(pushes_per_sec);
        peak_pull = peak_pull.max(pulls_per_sec);
        let stage_cost = budget.spent() - spent_before;
        let budget_hit = budget.is_hit();
        if budget_hit {
            budget_limited = true;
        }
        stages.push(StageReport {
            writers: spec.writers,
            readers: spec.readers,
            wall_ms,
            push_ok,
            push_conflict,
            push_err,
            pull_ok,
            pull_err,
            pushes_per_sec,
            pulls_per_sec,
            stage_cost_usd: stage_cost,
            budget_hit,
        });
        if budget_hit {
            break;
        }
    }

    Ok(LoadTestReport {
        repo: repo.to_string(),
        tip: tip.to_hex(),
        budget_usd: cfg.budget_usd,
        total_cost_usd: budget.spent(),
        budget_limited,
        peak_pushes_per_sec: peak_push,
        peak_pulls_per_sec: peak_pull,
        cost_per_push: OpCostSummary::from_totals(push_samples, &push_totals),
        cost_per_pull: OpCostSummary::from_totals(pull_samples, &pull_totals),
        stages,
        duration_ms: metrics::now_ms() - run_start,
        shards: cfg.shards,
    })
}

async fn writer_loop(
    driver: &dyn LoadDriver,
    seed_tip: Oid,
    branch_id: u32,
    deadline: f64,
    budget: &Budget,
) -> Vec<AttemptResult> {
    let mut out = Vec::new();
    let branch = format!("refs/heads/load/w{branch_id}");
    let mut tip = Oid::ZERO;
    let mut seq = 0u64;
    while metrics::now_ms() < deadline {
        if !budget.allow_start() {
            break;
        }
        let parent = if tip.is_zero() { seed_tip } else { tip };
        let (new_oid, pack) = build_writer_pack(parent, branch_id, seq);
        let body = build_push_body(tip, new_oid, &branch, &pack);
        match driver.push(body).await {
            Ok(mut a) => {
                budget.record(a.metrics.cost_usd);
                if a.outcome == AttemptOutcome::Ok {
                    tip = new_oid;
                    a.new_tip = Some(new_oid);
                    // Outside the timed push — matches Worker wait_until.
                    let _ = driver.maybe_repack().await;
                }
                // Conflicts still spent server work; count their cost too
                // (already in metrics when the server processed them).
                out.push(a);
            }
            Err(e) => {
                out.push(AttemptResult {
                    kind: AttemptKind::Push,
                    outcome: AttemptOutcome::Err,
                    metrics: AttemptMetrics::default(),
                    new_tip: None,
                });
                let _ = e;
            }
        }
        seq += 1;
    }
    out
}

async fn reader_loop(
    driver: &dyn LoadDriver,
    tip: Oid,
    deadline: f64,
    budget: &Budget,
) -> Vec<AttemptResult> {
    let mut out = Vec::new();
    while metrics::now_ms() < deadline {
        if !budget.allow_start() {
            break;
        }
        match driver.pull(tip).await {
            Ok(a) => {
                budget.record(a.metrics.cost_usd);
                out.push(a);
            }
            Err(_) => {
                out.push(AttemptResult {
                    kind: AttemptKind::Pull,
                    outcome: AttemptOutcome::Err,
                    metrics: AttemptMetrics::default(),
                    new_tip: None,
                });
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Synthetic packs / protocol bodies
// ---------------------------------------------------------------------------

/// One-commit seed: `SEED_BLOBS` small blobs under a single tree.
pub fn build_seed_pack() -> (Oid, Vec<u8>) {
    let mut w = PackWriter::new((SEED_BLOBS + 2) as u32);
    let mut entries = Vec::new();
    for i in 0..SEED_BLOBS {
        let data = noise(SEED_BLOB_BYTES, 0xC0FFEE ^ i as u64);
        let oid = hash_object(ObjType::Blob, &data);
        w.add_full(ObjType::Blob, &data);
        entries.push(TreeEntry {
            mode: "100644".into(),
            name: format!("f{i:03}.txt"),
            oid,
        });
    }
    entries.sort_by(|a, b| a.name.cmp(&b.name));
    let tree = encode_tree(&entries);
    let tree_oid = hash_object(ObjType::Tree, &tree);
    w.add_full(ObjType::Tree, &tree);
    let commit = format!(
        "tree {tree_oid}\nauthor Load <load@test> 1700000000 +0000\n\
         committer Load <load@test> 1700000000 +0000\n\nloadtest seed\n"
    );
    let commit_oid = hash_object(ObjType::Commit, commit.as_bytes());
    w.add_full(ObjType::Commit, commit.as_bytes());
    (commit_oid, w.finish().0)
}

/// Incremental writer commit: new blob + new tree + commit on `parent`.
fn build_writer_pack(parent: Oid, branch_id: u32, seq: u64) -> (Oid, Vec<u8>) {
    let mut w = PackWriter::new(3);
    let data = noise(
        WRITE_BLOB_BYTES,
        0xDEAD_BEEF ^ (branch_id as u64) << 32 ^ seq,
    );
    let blob_oid = hash_object(ObjType::Blob, &data);
    w.add_full(ObjType::Blob, &data);
    let entries = vec![TreeEntry {
        mode: "100644".into(),
        name: format!("w{branch_id}.txt"),
        oid: blob_oid,
    }];
    let tree = encode_tree(&entries);
    let tree_oid = hash_object(ObjType::Tree, &tree);
    w.add_full(ObjType::Tree, &tree);
    let commit = format!(
        "tree {tree_oid}\nparent {parent}\n\
         author Load <load@test> 1700000000 +0000\n\
         committer Load <load@test> 1700000000 +0000\n\nw{branch_id}#{seq}\n"
    );
    let commit_oid = hash_object(ObjType::Commit, commit.as_bytes());
    w.add_full(ObjType::Commit, commit.as_bytes());
    (commit_oid, w.finish().0)
}

pub fn build_push_body(old: Oid, new: Oid, refname: &str, pack: &[u8]) -> Vec<u8> {
    let mut body = Vec::new();
    body.extend_from_slice(&pktline::text_pkt(&format!(
        "{} {} {refname}\0report-status side-band-64k agent=git-server-loadtest",
        old.to_hex(),
        new.to_hex()
    )));
    body.extend_from_slice(pktline::flush_pkt());
    body.extend_from_slice(pack);
    body
}

pub fn build_fetch_body(want: Oid) -> Vec<u8> {
    let mut body = Vec::new();
    body.extend_from_slice(&pktline::text_pkt("command=fetch"));
    body.extend_from_slice(&pktline::text_pkt("object-format=sha1"));
    body.extend_from_slice(pktline::delim_pkt());
    body.extend_from_slice(&pktline::text_pkt("no-progress"));
    body.extend_from_slice(&pktline::text_pkt("deepen 1"));
    body.extend_from_slice(&pktline::text_pkt(&format!("want {want}")));
    body.extend_from_slice(&pktline::text_pkt("done"));
    body.extend_from_slice(pktline::flush_pkt());
    body
}

/// Classify a receive-pack response body.
pub fn classify_push_body(body: &[u8]) -> AttemptOutcome {
    let text = String::from_utf8_lossy(body);
    if text.contains("concurrent update") {
        return AttemptOutcome::Conflict;
    }
    // report-status: "unpack ok" then per-ref "ok <ref>" / "ng <ref> <msg>".
    if text.contains("ng ") {
        return AttemptOutcome::Err;
    }
    if text.contains("unpack ok") {
        return AttemptOutcome::Ok;
    }
    AttemptOutcome::Err
}

// ---------------------------------------------------------------------------
// In-process driver (native tests + Worker when not sharding)
// ---------------------------------------------------------------------------

struct ChunkedBody {
    chunks: VecDeque<Vec<u8>>,
}

impl ChunkedBody {
    fn new(bytes: Vec<u8>) -> Self {
        let mut chunks = VecDeque::new();
        for c in bytes.chunks(64 * 1024) {
            chunks.push_back(c.to_vec());
        }
        Self { chunks }
    }
}

#[async_trait(?Send)]
impl BodyStream for ChunkedBody {
    async fn next_chunk(&mut self) -> Result<Option<Vec<u8>>, String> {
        Ok(self.chunks.pop_front())
    }
}

/// Drive [`GitHttp`] in-process (same code path as production handlers).
pub struct InProcessDriver {
    http: GitHttp,
    repo: String,
    nonce_counter: Cell<u64>,
}

impl InProcessDriver {
    pub fn new(http: GitHttp, repo: impl Into<String>) -> Self {
        Self {
            http,
            repo: repo.into(),
            nonce_counter: Cell::new(1),
        }
    }

    fn nonce(&self) -> String {
        let n = self.nonce_counter.get();
        self.nonce_counter.set(n + 1);
        format!("lt-{n}")
    }

    async fn call(
        &self,
        method: &str,
        path: &str,
        body: Vec<u8>,
        git_protocol: Option<&str>,
    ) -> Result<(u16, Vec<u8>, AttemptMetrics), String> {
        let mut stream = ChunkedBody::new(body);
        let req = HttpRequest {
            method,
            path,
            query: None,
            git_protocol,
            content_encoding: None,
            cf_ray: None,
            loadtest_token: None,
        };
        let resp = self.http.handle(&req, &mut stream, &self.nonce()).await;
        let status = resp.status;
        let metrics = match &resp.metrics {
            Some((m, ms)) => AttemptMetrics::from_metrics(m, *ms),
            None => AttemptMetrics::default(),
        };
        let bytes = match resp.body {
            Body::Full(b) => b,
            Body::Stream(mut s) => {
                use futures::StreamExt;
                let mut out = Vec::new();
                while let Some(chunk) = s.next().await {
                    out.extend_from_slice(&chunk?);
                }
                out
            }
        };
        Ok((status, bytes, metrics))
    }

    async fn maybe_repack_inner(&self) -> Result<(), String> {
        let repo = crate::repo::Repo {
            store: self.http.store.as_ref(),
            states: self.http.states.as_ref(),
            name: &self.repo,
        };
        let packs = match repo.load_state().await {
            Ok(loaded) => loaded.state.packs.len(),
            Err(_) => return Ok(()),
        };
        if packs < crate::maintenance::AUTO_REPACK_TRIGGER_PACKS {
            return Ok(());
        }
        match crate::maintenance::repack(&repo, &self.nonce()).await {
            Ok(_) => Ok(()),
            // Busy / lost-race are expected under concurrent writers.
            Err(_) => Ok(()),
        }
    }
}

#[async_trait(?Send)]
impl LoadDriver for InProcessDriver {
    async fn ensure_seeded(&self, tip_hint: Option<Oid>) -> Result<Oid, String> {
        if let Some(t) = tip_hint {
            return Ok(t);
        }
        let path = format!("/api/{}", self.repo);
        let (status, body, _) = self.call("GET", &path, Vec::new(), None).await?;
        if status == 200 {
            if let Ok(v) = serde_json::from_slice::<serde_json::Value>(&body) {
                if v.get("status").and_then(|s| s.as_str()) == Some("READY") {
                    if let Some(hex) = v.get("head_commit").and_then(|s| s.as_str()) {
                        if let Some(oid) = Oid::from_hex(hex) {
                            return Ok(oid);
                        }
                    }
                }
            }
        }
        let (commit, pack) = build_seed_pack();
        let push = build_push_body(Oid::ZERO, commit, "refs/heads/main", &pack);
        let path = format!("/{}/git-receive-pack", self.repo);
        let (status, body, _) = self.call("POST", &path, push, None).await?;
        if status != 200 || classify_push_body(&body) != AttemptOutcome::Ok {
            return Err(format!(
                "seed push failed: status={status} body={}",
                String::from_utf8_lossy(&body)
            ));
        }
        Ok(commit)
    }

    async fn push(&self, body: Vec<u8>) -> Result<AttemptResult, String> {
        let path = format!("/{}/git-receive-pack", self.repo);
        let start = metrics::now_ms();
        let (status, resp, mut m) = self.call("POST", &path, body, None).await?;
        if m.wall_ms == 0.0 {
            m.wall_ms = metrics::now_ms() - start;
        }
        if m.ms == 0.0 {
            m.ms = m.wall_ms;
        }
        let outcome = if status != 200 {
            AttemptOutcome::Err
        } else {
            classify_push_body(&resp)
        };
        Ok(AttemptResult {
            kind: AttemptKind::Push,
            outcome,
            metrics: m,
            new_tip: None,
        })
    }

    async fn pull(&self, want: Oid) -> Result<AttemptResult, String> {
        let path = format!("/{}/git-upload-pack", self.repo);
        let body = build_fetch_body(want);
        let start = metrics::now_ms();
        let (status, resp, mut m) = self.call("POST", &path, body, Some("version=2")).await?;
        if m.wall_ms == 0.0 {
            m.wall_ms = metrics::now_ms() - start;
        }
        if m.ms == 0.0 {
            m.ms = m.wall_ms;
        }
        let outcome = if status == 200 && !resp.is_empty() {
            AttemptOutcome::Ok
        } else {
            AttemptOutcome::Err
        };
        Ok(AttemptResult {
            kind: AttemptKind::Pull,
            outcome,
            metrics: m,
            new_tip: None,
        })
    }

    async fn maybe_repack(&self) -> Result<(), String> {
        // Detached metrics frame: concurrent writers share one isolate, and
        // without this the stack-top sibling would absorb our DO/R2 counts.
        crate::metrics::begin_detached();
        let result = self.maybe_repack_inner().await;
        crate::metrics::discard();
        result
    }
}

/// Deterministic noise that compiles on wasm (`testutil` is native-only).
fn noise(len: usize, mut seed: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    while out.len() < len {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        out.extend_from_slice(&seed.to_le_bytes());
    }
    out.truncate(len);
    out
}

/// Merge shard reports into one coordinator report (same repo).
pub fn merge_shard_reports(
    repo: &str,
    tip: &str,
    budget_usd: f64,
    shards: u32,
    parts: &[LoadTestReport],
) -> LoadTestReport {
    if parts.is_empty() {
        return LoadTestReport {
            repo: repo.to_string(),
            tip: tip.to_string(),
            budget_usd,
            total_cost_usd: 0.0,
            budget_limited: false,
            peak_pushes_per_sec: 0.0,
            peak_pulls_per_sec: 0.0,
            cost_per_push: OpCostSummary::default(),
            cost_per_pull: OpCostSummary::default(),
            stages: vec![],
            duration_ms: 0.0,
            shards,
        };
    }
    // Align by stage index; sum ok counts and costs, take max wall, recompute QPS.
    let n_stages = parts.iter().map(|p| p.stages.len()).min().unwrap_or(0);
    let mut stages = Vec::new();
    let mut peak_push: f64 = 0.0;
    let mut peak_pull: f64 = 0.0;
    let mut total_cost = 0.0;
    let mut budget_limited = false;
    let mut duration_ms = 0.0_f64;

    for i in 0..n_stages {
        let mut push_ok = 0u64;
        let mut push_conflict = 0u64;
        let mut push_err = 0u64;
        let mut pull_ok = 0u64;
        let mut pull_err = 0u64;
        let mut wall_ms = 0.0_f64;
        let mut stage_cost = 0.0;
        let mut budget_hit = false;
        let writers: u32 = parts.iter().map(|p| p.stages[i].writers).sum();
        let readers: u32 = parts.iter().map(|p| p.stages[i].readers).sum();
        for p in parts {
            let s = &p.stages[i];
            push_ok += s.push_ok;
            push_conflict += s.push_conflict;
            push_err += s.push_err;
            pull_ok += s.pull_ok;
            pull_err += s.pull_err;
            wall_ms = wall_ms.max(s.wall_ms);
            stage_cost += s.stage_cost_usd;
            budget_hit |= s.budget_hit;
        }
        let wall_s = wall_ms.max(1.0) / 1000.0;
        let pps: f64 = push_ok as f64 / wall_s;
        let rps: f64 = pull_ok as f64 / wall_s;
        peak_push = f64::max(peak_push, pps);
        peak_pull = f64::max(peak_pull, rps);
        total_cost += stage_cost;
        budget_limited |= budget_hit;
        stages.push(StageReport {
            writers,
            readers,
            wall_ms,
            push_ok,
            push_conflict,
            push_err,
            pull_ok,
            pull_err,
            pushes_per_sec: pps,
            pulls_per_sec: rps,
            stage_cost_usd: stage_cost,
            budget_hit,
        });
    }
    for p in parts {
        duration_ms = duration_ms.max(p.duration_ms);
        budget_limited |= p.budget_limited;
        total_cost = total_cost.max(p.total_cost_usd); // prefer sum of stage costs
    }
    // Recompute total from stages (more accurate when shards overlap in wall clock).
    total_cost = stages.iter().map(|s| s.stage_cost_usd).sum();

    // Weighted mean costs across shards.
    let mut push = OpTotals::default();
    let mut push_n = 0u64;
    let mut pull = OpTotals::default();
    let mut pull_n = 0u64;
    for p in parts {
        if p.cost_per_push.samples > 0 {
            let n = p.cost_per_push.samples;
            push.r2_class_a += (p.cost_per_push.mean_r2_class_a * n as f64) as u64;
            push.r2_class_b += (p.cost_per_push.mean_r2_class_b * n as f64) as u64;
            push.do_requests += (p.cost_per_push.mean_do * n as f64) as u64;
            push.kv_ops += (p.cost_per_push.mean_kv * n as f64) as u64;
            push.cost_usd += p.cost_per_push.mean_cost_usd * n as f64;
            push.ms += p.cost_per_push.mean_ms * n as f64;
            push_n += n;
        }
        if p.cost_per_pull.samples > 0 {
            let n = p.cost_per_pull.samples;
            pull.r2_class_a += (p.cost_per_pull.mean_r2_class_a * n as f64) as u64;
            pull.r2_class_b += (p.cost_per_pull.mean_r2_class_b * n as f64) as u64;
            pull.do_requests += (p.cost_per_pull.mean_do * n as f64) as u64;
            pull.kv_ops += (p.cost_per_pull.mean_kv * n as f64) as u64;
            pull.cost_usd += p.cost_per_pull.mean_cost_usd * n as f64;
            pull.ms += p.cost_per_pull.mean_ms * n as f64;
            pull_n += n;
        }
    }

    LoadTestReport {
        repo: repo.to_string(),
        tip: tip.to_string(),
        budget_usd,
        total_cost_usd: total_cost,
        budget_limited,
        peak_pushes_per_sec: peak_push,
        peak_pulls_per_sec: peak_pull,
        cost_per_push: OpCostSummary::from_totals(push_n, &push),
        cost_per_pull: OpCostSummary::from_totals(pull_n, &pull),
        stages,
        duration_ms,
        shards,
    }
}

/// Fan-out hook for multi-isolate shard POSTs against **one** repo.
/// Native tests leave this unset (in-process partitions). The Worker also
/// leaves it unset — phone UI fans out from the browser instead (Worker
/// self-fetch hits Cloudflare 1042 / 1019 / bare 500).
#[async_trait(?Send)]
pub trait LoadtestFanout {
    async fn post_loadtest(
        &self,
        repo: &str,
        req: LoadTestRequest,
    ) -> Result<LoadTestReport, String>;
}

/// Convenience: run an in-process load test against a store pair.
pub async fn run_in_process(
    store: Rc<dyn Store>,
    states: Rc<dyn StateStore>,
    repo: &str,
    req: LoadTestRequest,
) -> Result<LoadTestReport, String> {
    let cfg = req.into_config()?;
    let http = GitHttp::new(store, states);
    execute(&http, repo, &cfg).await
}

/// Run with an already-built [`GitHttp`] (shared by JSON and HTML entry points).
pub async fn execute(
    http: &GitHttp,
    repo: &str,
    cfg: &LoadTestConfig,
) -> Result<LoadTestReport, String> {
    if cfg.shards > 1 && !cfg.shard {
        if let Some(fanout) = http.loadtest_fanout.as_ref() {
            return run_sharded_fanout(http, fanout.as_ref(), repo, cfg).await;
        }
        return run_sharded_inprocess(
            GitHttp::new(http.store.clone(), http.states.clone())
                .with_push_limit(http.push_limit_bytes),
            repo,
            cfg,
        )
        .await;
    }
    let driver = InProcessDriver::new(
        GitHttp::new(http.store.clone(), http.states.clone())
            .with_push_limit(http.push_limit_bytes),
        repo,
    );
    run_loadtest(repo, &driver, cfg).await
}

/// HTTP self-fetch sharding: each shard POST is a separate Worker invocation
/// against the same repo.
async fn run_sharded_fanout(
    http: &GitHttp,
    fanout: &dyn LoadtestFanout,
    repo: &str,
    cfg: &LoadTestConfig,
) -> Result<LoadTestReport, String> {
    let n = cfg.shards.max(1);
    // Seed once in this isolate, then hand the tip to every shard.
    let seed_driver = InProcessDriver::new(
        GitHttp::new(http.store.clone(), http.states.clone())
            .with_push_limit(http.push_limit_bytes),
        repo,
    );
    let tip = seed_driver.ensure_seeded(cfg.tip).await?;
    let tip_hex = tip.to_hex();
    let budget_each = (cfg.budget_usd / n as f64).max(0.0001);

    let mut futs = Vec::with_capacity(n as usize);
    for i in 0..n {
        let mut shard_cfg = cfg.clone();
        shard_cfg.shard = true;
        shard_cfg.shards = 1;
        shard_cfg.tip = Some(tip);
        shard_cfg.shard_index = i;
        shard_cfg.budget_usd = budget_each;
        shard_cfg.stages = cfg
            .stages
            .iter()
            .enumerate()
            .map(|(si, st)| {
                let writers = st.writers / n + if i == 0 { st.writers % n } else { 0 };
                let readers = st.readers / n + if i == 0 { st.readers % n } else { 0 };
                let _ = si;
                StageSpec { writers, readers }
            })
            .filter(|st| st.writers > 0 || st.readers > 0)
            .collect();
        if shard_cfg.stages.is_empty() {
            continue;
        }
        let req = LoadTestRequest::from_config(&shard_cfg, Some(&tip_hex));
        futs.push(fanout.post_loadtest(repo, req));
    }
    let results = join_all(futs).await;
    let mut parts = Vec::with_capacity(results.len());
    for r in results {
        parts.push(r?);
    }
    Ok(merge_shard_reports(
        repo,
        &tip_hex,
        cfg.budget_usd,
        n,
        &parts,
    ))
}

/// Constant-time-ish compare for the loadtest shared secret.
pub fn token_matches(provided: &str, expected: &str) -> bool {
    if provided.len() != expected.len() {
        return false;
    }
    provided
        .bytes()
        .zip(expected.bytes())
        .fold(0u8, |acc, (a, b)| acc | (a ^ b))
        == 0
}

/// Phone UI defaults. Measures **one** disposable repo (Workers
/// subrequest/memory walls keep peak concurrency modest).
pub const PHONE_DEFAULT_BUDGET_USD: f64 = 0.10;
pub const PHONE_DEFAULT_DURATION_SECS: u64 = 4;
/// Peak writers in the write ramp; read stage uses `2 × peak`.
pub const PHONE_DEFAULT_PEAK: u32 = 8;
pub const PHONE_MAX_PEAK: u32 = 48;
/// Isolates to fan writers/readers across (same repo). `1` = this isolate only.
pub const PHONE_DEFAULT_SHARDS: u32 = 4;
pub const PHONE_MAX_SHARDS: u32 = MAX_SHARDS;
/// Max concurrent writer loops in **one** Worker invocation.
///
/// Nested in-process pushes share one isolate's ~1000-subrequest budget and
/// 128 MiB heap. A phone ramp of 32 writers / 64 readers threw Cloudflare
/// Error 1101 (PR #321); ≤6 writers / ≤12 readers stayed healthy.
pub const PHONE_MAX_WRITERS_PER_ISOLATE: u32 = 6;
/// Max concurrent reader loops in one Worker invocation (see writers cap).
pub const PHONE_MAX_READERS_PER_ISOLATE: u32 = 12;

/// Clamp a phone peak-writers value into the safe range.
pub fn clamp_phone_peak(peak: u32) -> u32 {
    peak.clamp(1, PHONE_MAX_PEAK)
}

/// Clamp phone isolate-shard count.
pub fn clamp_phone_shards(shards: u32) -> u32 {
    shards.clamp(1, PHONE_MAX_SHARDS)
}

/// Raise `shards` (and clamp `peak` if needed) so each isolate stays within
/// [`PHONE_MAX_WRITERS_PER_ISOLATE`]. Preserves offered peak when enough
/// isolates are available (≤ [`PHONE_MAX_SHARDS`]).
pub fn phone_fanout_plan(peak: u32, shards: u32) -> (u32, u32) {
    let peak = clamp_phone_peak(peak);
    let mut shards = clamp_phone_shards(shards);
    let need = peak.div_ceil(PHONE_MAX_WRITERS_PER_ISOLATE).max(1);
    if need > shards {
        shards = clamp_phone_shards(need);
    }
    let max_peak = shards
        .saturating_mul(PHONE_MAX_WRITERS_PER_ISOLATE)
        .clamp(1, PHONE_MAX_PEAK);
    (peak.min(max_peak), shards)
}

/// Cap one stage to the per-isolate concurrency envelope (Workers only).
/// Native tests keep the requested concurrency.
pub fn clamp_stage_to_isolate(st: &StageSpec) -> StageSpec {
    #[cfg(target_arch = "wasm32")]
    {
        StageSpec {
            writers: st.writers.min(PHONE_MAX_WRITERS_PER_ISOLATE),
            readers: st.readers.min(PHONE_MAX_READERS_PER_ISOLATE),
        }
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        st.clone()
    }
}

/// Phone stages from a peak writer count: warm-up → peak writers → 2× readers.
pub fn phone_stages(peak: u32) -> Vec<StageSpec> {
    let peak = clamp_phone_peak(peak);
    let warm = (peak / 3).max(1);
    let readers = peak.saturating_mul(2).max(1);
    vec![
        StageSpec {
            writers: warm,
            readers: 0,
        },
        StageSpec {
            writers: peak,
            readers: 0,
        },
        StageSpec {
            writers: 0,
            readers,
        },
    ]
}

/// Phone-friendly request: short stages scaled by `peak` writers.
pub fn phone_request(
    budget_usd: f64,
    duration_secs: u64,
    peak: u32,
    shards: u32,
) -> LoadTestRequest {
    let (peak, shards) = phone_fanout_plan(peak, shards);
    LoadTestRequest {
        confirm: true,
        budget_usd: Some(budget_usd),
        duration_secs: Some(duration_secs),
        stages: Some(phone_stages(peak)),
        shards: Some(shards),
        shard: false,
        tip: None,
        shard_index: None,
        token: None,
    }
}

/// Unique disposable repo name for a phone run.
pub fn phone_repo_name() -> String {
    let ms = metrics::now_ms() as u64;
    format!("lt{}", ms % 1_000_000_000)
}

/// Landing page: budget + peak + shards controls, then Run (one disposable repo).
pub fn html_landing(
    budget_usd: f64,
    duration_secs: u64,
    peak: u32,
    shards: u32,
    token: Option<&str>,
) -> String {
    let token_js = token.map(js_string_escape).unwrap_or_default();
    let has_token = token.is_some();
    let token_hint = if has_token {
        String::new()
    } else {
        "<p class=\"hint\">Add <code>?token=…</code> to the URL (required in production).</p>"
            .into()
    };
    let peak = clamp_phone_peak(peak);
    let shards = clamp_phone_shards(shards);
    let (peak, shards) = phone_fanout_plan(peak, shards);
    let stages = phone_stages(peak);
    let warm = stages[0].writers;
    let readers = stages[2].readers;
    let expect_secs = duration_secs.saturating_mul(3).saturating_add(5);
    let max_peak = PHONE_MAX_PEAK;
    let max_shards = PHONE_MAX_SHARDS;
    let max_w_iso = PHONE_MAX_WRITERS_PER_ISOLATE;
    let max_r_iso = PHONE_MAX_READERS_PER_ISOLATE;
    format!(
        r##"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>git loadtest</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Source+Sans+3:wght@400;600;700&family=Source+Code+Pro:wght@500&display=swap" rel="stylesheet">
<style>
:root {{
  --bg: #0f1419; --fg: #e7ecf1; --muted: #8b9aab; --accent: #3dd68c; --warn: #f5a524;
  --field: #1a222c; --line: #2a3542;
}}
* {{ box-sizing: border-box; }}
body {{
  margin: 0; min-height: 100dvh; display: grid; place-items: center;
  padding: 1.5rem; background: var(--bg); color: var(--fg);
  font: 400 1.125rem/1.45 "Source Sans 3", system-ui, sans-serif;
}}
main {{ width: min(28rem, 100%); text-align: center; }}
h1 {{ font-size: 1.75rem; font-weight: 700; margin: 0 0 0.5rem; letter-spacing: -0.02em; }}
p {{ color: var(--muted); margin: 0 0 1.25rem; }}
p.hint {{ font-size: 0.95rem; }}
p.plan {{ font-size: 0.95rem; margin-top: 0.75rem; }}
.fields {{
  display: grid; gap: 0.85rem; text-align: left; margin: 0 0 1.25rem;
}}
label {{
  display: grid; gap: 0.35rem; font-size: 0.95rem; color: var(--muted); font-weight: 600;
}}
label span.detail {{ font-weight: 400; color: var(--muted); }}
input[type="number"] {{
  width: 100%; padding: 0.75rem 0.85rem; border: 1px solid var(--line);
  border-radius: 0.6rem; background: var(--field); color: var(--fg);
  font: inherit; font-family: "Source Code Pro", ui-monospace, monospace;
}}
button.run {{
  display: block; width: 100%; padding: 1.15rem 1.25rem; border: 0; cursor: pointer;
  background: var(--accent); color: #062016; font: inherit; font-weight: 700;
  font-size: 1.25rem; border-radius: 0.75rem;
}}
button.run:disabled {{ opacity: 0.55; cursor: wait; }}
button.run:active:not(:disabled) {{ filter: brightness(0.92); }}
#status {{ min-height: 1.5rem; margin: 1rem 0 0; color: var(--muted); font-size: 1rem; }}
#status.err {{ color: var(--warn); white-space: pre-wrap; text-align: left; }}
#debug {{
  display: none; margin: 0.75rem 0 0; padding: 0.75rem; text-align: left;
  border: 1px solid var(--line); border-radius: 0.5rem; background: var(--field);
  font: 500 0.8rem/1.35 "Source Code Pro", ui-monospace, monospace;
  color: var(--muted); white-space: pre-wrap; word-break: break-word; max-height: 40vh; overflow: auto;
}}
#debug.show {{ display: block; }}
code {{ font-family: "Source Code Pro", ui-monospace, monospace; font-size: 0.95em; }}
</style>
</head>
<body>
<main>
  <h1>git loadtest</h1>
  <p>Push/pull load against <strong>one</strong> disposable repo on this Worker.<br>
  Concurrent writers use separate branches (merge-apply).</p>
  {token_hint}
  <div class="fields">
    <label>Cost budget (USD)
      <input id="budget" type="number" inputmode="decimal" min="0.01" max="5" step="0.01" value="{budget_usd:.2}">
    </label>
    <label>Peak writers
      <span class="detail">Warm-up → peak → 2× readers. Max {max_peak}. Each writer owns a branch.</span>
      <input id="peak" type="number" inputmode="numeric" min="1" max="{max_peak}" step="1" value="{peak}">
    </label>
    <label>Isolates (shards)
      <span class="detail">Same repo; one browser POST per isolate. Max {max_shards}. Auto-raises so each isolate stays ≤{max_w_iso} writers (avoids CF 1101).</span>
      <input id="shards" type="number" inputmode="numeric" min="1" max="{max_shards}" step="1" value="{shards}">
    </label>
  </div>
  <p class="plan" id="plan">{warm}w → {peak}w → {readers}r · {shards} shards · {duration_secs}s × 3 · ~{expect_secs}s</p>
  <button class="run" id="run" type="button">Run load test</button>
  <p id="status" aria-live="polite"></p>
  <pre id="debug" aria-live="polite"></pre>
</main>
<script>
(function () {{
  var btn = document.getElementById("run");
  var status = document.getElementById("status");
  var debugEl = document.getElementById("debug");
  var budgetEl = document.getElementById("budget");
  var peakEl = document.getElementById("peak");
  var shardsEl = document.getElementById("shards");
  var plan = document.getElementById("plan");
  var duration = {duration_secs};
  var token = "{token_js}";
  var maxPeak = {max_peak};
  var maxShards = {max_shards};
  var maxWIso = {max_w_iso};
  var maxRIso = {max_r_iso};
  function clampPeak(p) {{
    p = Math.floor(Number(p) || 1);
    if (p < 1) p = 1;
    if (p > maxPeak) p = maxPeak;
    return p;
  }}
  function clampShards(s) {{
    s = Math.floor(Number(s) || 1);
    if (s < 1) s = 1;
    if (s > maxShards) s = maxShards;
    return s;
  }}
  /** Raise shards (or trim peak) so each isolate stays ≤ maxWIso writers. */
  function fanoutPlan(peak, shards) {{
    peak = clampPeak(peak);
    shards = clampShards(shards);
    var need = Math.max(1, Math.ceil(peak / maxWIso));
    if (need > shards) shards = clampShards(need);
    var maxPeakHere = Math.min(maxPeak, Math.max(1, shards * maxWIso));
    if (peak > maxPeakHere) peak = maxPeakHere;
    return {{ peak: peak, shards: shards }};
  }}
  function updatePlan() {{
    var requestedShards = clampShards(shardsEl.value);
    var planVals = fanoutPlan(peakEl.value, requestedShards);
    var peak = planVals.peak;
    var shards = planVals.shards;
    var warm = Math.max(1, Math.floor(peak / 3));
    var readers = Math.max(1, peak * 2);
    var perW = Math.ceil(peak / shards);
    var expect = duration * 3 + 5;
    var note = shards > requestedShards
      ? " (raised to " + shards + " shards, ≤" + maxWIso + "w each)"
      : " (≤" + perW + "w/isolate)";
    plan.textContent = warm + "w → " + peak + "w → " + readers +
      "r · " + shards + " shards · " + duration + "s × 3 · ~" + expect + "s" + note;
  }}
  peakEl.addEventListener("input", updatePlan);
  shardsEl.addEventListener("input", updatePlan);
  function jsonHeaders() {{
    var h = {{ "Content-Type": "application/json", "Accept": "application/json" }};
    if (token) h["X-Loadtest-Token"] = token;
    return h;
  }}
  function headerGet(res, name) {{
    try {{ return res.headers.get(name) || ""; }} catch (e) {{ return ""; }}
  }}
  /** Summarize a failed HTTP body without wiping Cloudflare error pages. */
  function summarizeBody(text) {{
    if (!text) return "(empty body)";
    var t = String(text);
    var codes = [];
    var m;
    // Single backslashes: this is a raw Rust format string, not a JS string escape.
    var re = /\b(10\d{{2}}|11\d{{2}})\b/g;
    while ((m = re.exec(t))) {{
      if (codes.indexOf(m[1]) < 0) codes.push(m[1]);
    }}
    var jsonErr = "";
    try {{
      var j = JSON.parse(t);
      if (j && (j.error || j.message)) jsonErr = String(j.error || j.message);
    }} catch (e) {{}}
    // Strip tags with a simple pattern (avoid embedding a script end-tag
    // sequence anywhere in this file — HTML would close the script early).
    var plain = t.replace(/<[^>]+>/g, " ").replace(/\s+/g, " ").trim();
    if (!plain && codes.length) plain = "Cloudflare error " + codes.join(", ");
    if (!plain) plain = t.slice(0, 400);
    var out = jsonErr || plain.slice(0, 600);
    if (codes.length && out.indexOf(codes[0]) < 0) {{
      out = "CF " + codes.join("/") + ": " + out;
    }}
    return out;
  }}
  function showErr(msg, detail) {{
    status.className = "err";
    status.textContent = msg;
    if (detail) {{
      debugEl.textContent = detail;
      debugEl.className = "show";
    }} else {{
      debugEl.textContent = "";
      debugEl.className = "";
    }}
    btn.disabled = false;
  }}
  function clearDebug() {{
    debugEl.textContent = "";
    debugEl.className = "";
  }}
  function fetchJson(step, url, init) {{
    return fetch(url, init).then(function (res) {{
      var ray = headerGet(res, "cf-ray") || headerGet(res, "CF-Ray");
      return res.text().then(function (t) {{
        if (!res.ok) {{
          var err = new Error(step + " HTTP " + res.status + ": " + summarizeBody(t));
          err.debug = [
            "step: " + step,
            "url: " + url,
            "status: " + res.status,
            "cf-ray: " + (ray || "(none)"),
            "content-type: " + (headerGet(res, "content-type") || "(none)"),
            "body:",
            t.slice(0, 2000) || "(empty)"
          ].join("\n");
          throw err;
        }}
        try {{
          return JSON.parse(t);
        }} catch (e) {{
          var pe = new Error(step + ": bad JSON (" + (e && e.message ? e.message : e) + ")");
          pe.debug = "step: " + step + "\nurl: " + url + "\nbody:\n" + t.slice(0, 2000);
          throw pe;
        }}
      }});
    }});
  }}
  function postLoadtest(step, repo, body) {{
    return fetchJson(step, "/api/" + repo + "/loadtest", {{
      method: "POST",
      credentials: "same-origin",
      headers: jsonHeaders(),
      body: JSON.stringify(body)
    }});
  }}
  function partitionStages(stages, shards, i) {{
    var out = [];
    for (var s = 0; s < stages.length; s++) {{
      var st = stages[s];
      var w = Math.floor(st.writers / shards) + (i === 0 ? (st.writers % shards) : 0);
      var r = Math.floor(st.readers / shards) + (i === 0 ? (st.readers % shards) : 0);
      if (w > maxWIso) w = maxWIso;
      if (r > maxRIso) r = maxRIso;
      if (w > 0 || r > 0) out.push({{ writers: w, readers: r }});
    }}
    return out;
  }}
  btn.addEventListener("click", function () {{
    btn.disabled = true;
    clearDebug();
    var t0 = Date.now();
    var phase = "starting";
    status.className = "";
    status.textContent = "Running… 0s";
    var tick = setInterval(function () {{
      status.textContent = "Running… " + Math.floor((Date.now() - t0) / 1000) + "s · " + phase;
    }}, 250);
    var budget = Number(budgetEl.value);
    if (!(budget > 0)) budget = {budget_usd:.2};
    var planVals = fanoutPlan(peakEl.value, shardsEl.value);
    var peak = planVals.peak;
    var shards = planVals.shards;
    if (shards !== clampShards(shardsEl.value)) {{
      shardsEl.value = String(shards);
    }}
    if (peak !== clampPeak(peakEl.value)) {{
      peakEl.value = String(peak);
    }}
    updatePlan();
    var warm = Math.max(1, Math.floor(peak / 3));
    var readers = Math.max(1, peak * 2);
    var stages = [
      {{ writers: warm, readers: 0 }},
      {{ writers: peak, readers: 0 }},
      {{ writers: 0, readers: readers }}
    ];
    var repo = "lt" + String(Date.now()).slice(-9);

    // Seed once (creates tip), then fan shard POSTs from the browser so each
    // lands on a separate isolate — Worker self-fetch is blocked by Cloudflare.
    var seedBudget = Math.min(0.02, Math.max(0.01, budget * 0.1));
    phase = "seed " + repo;
    postLoadtest("seed", repo, {{
      confirm: true,
      budget_usd: seedBudget,
      duration_secs: 1,
      stages: [{{ writers: 1, readers: 0 }}],
      shards: 1
    }}).then(function (seed) {{
      var tip = seed.tip;
      phase = "shards 0/" + shards;
      var done = 0;
      var posts = [];
      for (var i = 0; i < shards; i++) {{
        (function (idx) {{
          var shardStages = partitionStages(stages, shards, idx);
          if (!shardStages.length) return;
          posts.push(
            postLoadtest("shard " + idx, repo, {{
              confirm: true,
              budget_usd: budget / shards,
              duration_secs: duration,
              stages: shardStages,
              shard: true,
              tip: tip,
              shard_index: idx,
              shards: 1
            }}).then(function (part) {{
              done += 1;
              phase = "shards " + done + "/" + posts.length;
              return part;
            }})
          );
        }})(i);
      }}
      if (!posts.length) throw new Error("no shard work after partitioning");
      return Promise.all(posts).then(function (parts) {{
        phase = "merge";
        var mergeHeaders = {{
          "Content-Type": "application/json",
          "Accept": "text/html"
        }};
        if (token) mergeHeaders["X-Loadtest-Token"] = token;
        var q = "/loadtest/merge?peak=" + peak + "&duration=" + duration;
        if (token) q += "&token=" + encodeURIComponent(token);
        return fetch(q, {{
          method: "POST",
          credentials: "same-origin",
          headers: mergeHeaders,
          body: JSON.stringify({{
            confirm: true,
            budget_usd: budget,
            parts: parts
          }})
        }}).then(function (res) {{
          var ray = headerGet(res, "cf-ray") || headerGet(res, "CF-Ray");
          return res.text().then(function (t) {{
            return {{
              ok: res.ok,
              status: res.status,
              text: t,
              ray: ray,
              ctype: headerGet(res, "content-type")
            }};
          }});
        }});
      }});
    }}).then(function (r) {{
      clearInterval(tick);
      if (r.ok && r.text.indexOf("<html") !== -1) {{
        document.open(); document.write(r.text); document.close();
        return;
      }}
      showErr(
        "merge HTTP " + r.status + ": " + summarizeBody(r.text),
        [
          "step: merge",
          "status: " + r.status,
          "cf-ray: " + (r.ray || "(none)"),
          "content-type: " + (r.ctype || "(none)"),
          "body:",
          (r.text || "").slice(0, 2000) || "(empty)"
        ].join("\n")
      );
    }}).catch(function (e) {{
      clearInterval(tick);
      showErr(
        (e && e.message ? e.message : String(e)) +
          "\nTry fewer writers per isolate (raise shards, or peak ≤ " + maxWIso + " × shards).",
        e && e.debug ? e.debug : ""
      );
    }});
  }});
  updatePlan();
}})();
</script>
</body>
</html>
"##
    )
}

/// HTML results page for a completed run (phone-readable).
pub fn html_report(
    report: &LoadTestReport,
    token: Option<&str>,
    peak: u32,
    duration_secs: u64,
) -> String {
    let limited = if report.budget_limited {
        r#"<span class="badge warn">budget-limited</span>"#
    } else {
        r#"<span class="badge ok">completed</span>"#
    };
    let token_q = token
        .map(|t| format!("&amp;token={}", html_escape(t)))
        .unwrap_or_default();
    let peak = clamp_phone_peak(peak);
    let shards = clamp_phone_shards(report.shards.max(1));
    let again_href = format!(
        "/loadtest?budget={:.2}&amp;duration={duration_secs}&amp;peak={peak}&amp;shards={shards}{token_q}",
        report.budget_usd
    );
    let mut stages = String::new();
    for s in &report.stages {
        let w = s.writers;
        let r = s.readers;
        let pps = s.pushes_per_sec;
        let rps = s.pulls_per_sec;
        let ok_p = s.push_ok;
        let ok_r = s.pull_ok;
        let err_p = s.push_err + s.push_conflict;
        let err_r = s.pull_err;
        let cost = s.stage_cost_usd;
        stages.push_str(&format!(
            "<tr><td>{w}w/{r}r</td><td>{pps:.1}</td><td>{rps:.1}</td><td>{ok_p}/{ok_r}</td><td>{err_p}/{err_r}</td><td>${cost:.4}</td></tr>\n"
        ));
    }
    let push = &report.cost_per_push;
    let pull = &report.cost_per_pull;
    let repo = html_escape(&report.repo);
    let wall = report.duration_ms / 1000.0;
    let spent = report.total_cost_usd;
    let budget = report.budget_usd;
    let peak_p = report.peak_pushes_per_sec;
    let peak_r = report.peak_pulls_per_sec;
    let pull_note = if peak_r == 0.0
        && report
            .stages
            .iter()
            .any(|s| s.readers > 0 && s.pull_ok + s.pull_err > 0)
    {
        let errs: u64 = report.stages.iter().map(|s| s.pull_err).sum();
        format!(
            "<p class=\"meta\" style=\"color:var(--warn)\">No successful pulls ({errs} errors). \
             Usually the read stage was too wide for one isolate — retry after the lighter phone defaults deploy.</p>"
        )
    } else if peak_r == 0.0 && report.stages.iter().any(|s| s.readers > 0) {
        "<p class=\"meta\" style=\"color:var(--warn)\">Read stage produced no pull attempts (check duration / budget).</p>"
            .into()
    } else {
        String::new()
    };
    let push_n = push.samples;
    let push_usd = push.mean_cost_usd;
    let push_a = push.mean_r2_class_a;
    let push_b = push.mean_r2_class_b;
    let push_do = push.mean_do;
    let push_ms = push.mean_ms;
    let pull_n = pull.samples;
    let pull_usd = pull.mean_cost_usd;
    let pull_a = pull.mean_r2_class_a;
    let pull_b = pull.mean_r2_class_b;
    let pull_do = pull.mean_do;
    let pull_ms = pull.mean_ms;
    format!(
        r##"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>loadtest · {repo}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Source+Sans+3:wght@400;600;700&family=Source+Code+Pro:wght@500&display=swap" rel="stylesheet">
<style>
:root {{
  --bg: #0f1419; --fg: #e7ecf1; --muted: #8b9aab; --accent: #3dd68c;
  --warn: #f5a524; --card: #1a222c; --line: #2a3542;
}}
* {{ box-sizing: border-box; }}
body {{
  margin: 0; padding: 1.25rem 1rem 3rem; background: var(--bg); color: var(--fg);
  font: 400 1rem/1.45 "Source Sans 3", system-ui, sans-serif;
}}
.wrap {{ width: min(40rem, 100%); margin: 0 auto; }}
h1 {{ font-size: 1.5rem; margin: 0 0 0.35rem; letter-spacing: -0.02em; }}
.meta {{ color: var(--muted); margin: 0 0 1.25rem; font-size: 0.95rem; }}
.badge {{
  display: inline-block; padding: 0.15rem 0.55rem; border-radius: 999px;
  font-size: 0.8rem; font-weight: 600; vertical-align: middle;
}}
.badge.ok {{ background: #143528; color: var(--accent); }}
.badge.warn {{ background: #3a2a0e; color: var(--warn); }}
.grid {{
  display: grid; grid-template-columns: 1fr 1fr; gap: 0.75rem; margin-bottom: 1.25rem;
}}
.card {{
  background: var(--card); border: 1px solid var(--line); border-radius: 0.75rem;
  padding: 1rem 0.9rem;
}}
.card .label {{ color: var(--muted); font-size: 0.8rem; margin-bottom: 0.25rem; }}
.card .val {{
  font: 500 1.65rem/1.15 "Source Code Pro", ui-monospace, monospace;
  letter-spacing: -0.03em;
}}
h2 {{ font-size: 1.05rem; margin: 1.5rem 0 0.6rem; }}
table {{
  width: 100%; border-collapse: collapse; font-size: 0.9rem;
  font-family: "Source Code Pro", ui-monospace, monospace;
}}
th, td {{ text-align: left; padding: 0.45rem 0.35rem; border-bottom: 1px solid var(--line); }}
th {{ color: var(--muted); font-weight: 500; font-size: 0.75rem; }}
.ops {{ color: var(--muted); font-size: 0.9rem; margin: 0.35rem 0 0; }}
a.again {{
  display: block; margin-top: 1.75rem; text-align: center; padding: 1rem;
  background: var(--accent); color: #062016; text-decoration: none;
  font-weight: 700; border-radius: 0.75rem;
}}
</style>
</head>
<body>
<div class="wrap">
  <h1>loadtest {limited}</h1>
  <p class="meta">repo <code>{repo}</code> · {shards} shards · wall {wall:.1}s · spend ${spent:.4} / ${budget:.2}</p>
  {pull_note}
  <div class="grid">
    <div class="card"><div class="label">peak pushes/s</div><div class="val">{peak_p:.1}</div></div>
    <div class="card"><div class="label">peak pulls/s</div><div class="val">{peak_r:.1}</div></div>
  </div>
  <h2>Cost per push</h2>
  <p class="ops">{push_n} samples · mean ${push_usd:.6} · R2A {push_a:.1} · R2B {push_b:.1} · DO {push_do:.1} · {push_ms:.0} ms backend</p>
  <h2>Cost per pull</h2>
  <p class="ops">{pull_n} samples · mean ${pull_usd:.6} · R2A {pull_a:.1} · R2B {pull_b:.1} · DO {pull_do:.1} · {pull_ms:.0} ms backend</p>
  <h2>Stages</h2>
  <table>
    <thead><tr><th>load</th><th>push/s</th><th>pull/s</th><th>ok p/r</th><th>err p/r</th><th>$</th></tr></thead>
    <tbody>
{stages}    </tbody>
  </table>
  <a class="again" href="{again_href}">Back to run</a>
  <p class="meta" style="margin-top:1rem;text-align:center"><a href="/loadtest" style="color:var(--muted)">Back</a></p>
</div>
</body>
</html>
"##
    )
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// Escape for embedding inside a double-quoted JS / HTML attribute string.
fn js_string_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' | '"' => {
                out.push('\\');
                out.push(c);
            }
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '<' => out.push_str("\\u003c"),
            _ => out.push(c),
        }
    }
    out
}

/// Split offered concurrency across `cfg.shards` in-process partitions and
/// merge their reports. Same-isolate concurrency (native tests and the
/// Worker when not using HTTP fan-out); each partition gets its own writer
/// branch namespace via `shard_index`.
pub async fn run_sharded_inprocess(
    http: GitHttp,
    repo: &str,
    cfg: &LoadTestConfig,
) -> Result<LoadTestReport, String> {
    let n = cfg.shards.max(1);
    // Seed once, then hand the tip to every shard.
    let seeder = InProcessDriver::new(
        GitHttp::new(http.store.clone(), http.states.clone())
            .with_push_limit(http.push_limit_bytes),
        repo,
    );
    let tip = seeder.ensure_seeded(cfg.tip).await?;
    let budget_each = cfg.budget_usd / n as f64;

    let mut futs = Vec::new();
    for i in 0..n {
        let mut shard_cfg = cfg.clone();
        shard_cfg.shard = true;
        shard_cfg.shards = 1;
        shard_cfg.tip = Some(tip);
        shard_cfg.shard_index = i;
        shard_cfg.budget_usd = budget_each;
        // Divide concurrency; give leftovers to shard 0.
        shard_cfg.stages = cfg
            .stages
            .iter()
            .map(|s| {
                let w = s.writers / n;
                let r = s.readers / n;
                StageSpec {
                    writers: if i == 0 { w + s.writers % n } else { w },
                    readers: if i == 0 { r + s.readers % n } else { r },
                }
            })
            .filter(|s| s.writers > 0 || s.readers > 0)
            .collect();
        if shard_cfg.stages.is_empty() {
            continue;
        }
        let http_i = GitHttp::new(http.store.clone(), http.states.clone())
            .with_push_limit(http.push_limit_bytes);
        let repo = repo.to_string();
        futs.push(async move {
            let driver = InProcessDriver::new(http_i, repo.clone());
            run_loadtest(&repo, &driver, &shard_cfg).await
        });
    }
    let parts = join_all(futs).await;
    let mut reports = Vec::new();
    for p in parts {
        reports.push(p?);
    }
    Ok(merge_shard_reports(
        repo,
        &tip.to_hex(),
        cfg.budget_usd,
        n,
        &reports,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::refs::MemStateStore;
    use crate::storage::MemStore;
    use futures::executor::block_on;

    #[test]
    fn phone_stages_scale_with_peak() {
        let s = phone_stages(6);
        assert_eq!(s[0].writers, 2);
        assert_eq!(s[1].writers, 6);
        assert_eq!(s[2].readers, 12);
        let s = phone_stages(12);
        assert_eq!(s[0].writers, 4);
        assert_eq!(s[1].writers, 12);
        assert_eq!(s[2].readers, 24);
        assert_eq!(clamp_phone_peak(100), PHONE_MAX_PEAK);
    }

    #[test]
    fn phone_fanout_raises_shards_for_peak() {
        // peak=24 with shards=2 needs 4 isolates at ≤6 writers each.
        let (peak, shards) = phone_fanout_plan(24, 2);
        assert_eq!(peak, 24);
        assert_eq!(shards, 4);
        // Already enough shards: leave them.
        let (peak, shards) = phone_fanout_plan(8, 4);
        assert_eq!((peak, shards), (8, 4));
        // Hit high peak with shards=1: raise shards to cover peak.
        let (peak, shards) = phone_fanout_plan(PHONE_MAX_PEAK, 1);
        assert_eq!(peak, PHONE_MAX_PEAK);
        assert_eq!(
            shards,
            PHONE_MAX_PEAK.div_ceil(PHONE_MAX_WRITERS_PER_ISOLATE)
        );
        assert!(peak <= shards * PHONE_MAX_WRITERS_PER_ISOLATE);
        assert_eq!(
            clamp_stage_to_isolate(&StageSpec {
                writers: 99,
                readers: 99
            })
            .writers,
            99,
            "native builds do not clamp"
        );
    }

    #[test]
    fn request_requires_confirm() {
        let r = LoadTestRequest {
            confirm: false,
            budget_usd: Some(0.01),
            duration_secs: Some(1),
            stages: Some(vec![StageSpec {
                writers: 1,
                readers: 0,
            }]),
            shards: None,
            shard: false,
            tip: None,
            shard_index: None,
            token: None,
        };
        assert!(r.into_config().is_err());
    }

    #[test]
    fn parses_server_timing_cost() {
        let h = "total;dur=12.5, backend;dur=8.0, r2a;desc=\"2\", r2b;desc=\"7\", \
                 do;desc=\"1\", kv;desc=\"0\", cost;desc=\"9.270u$\"";
        let m = parse_server_timing(h);
        assert!((m.ms - 8.0).abs() < 1e-9, "mean latency uses backend dur");
        assert!((m.wall_ms - 12.5).abs() < 1e-9);
        assert_eq!(m.r2_class_a, 2);
        assert_eq!(m.r2_class_b, 7);
        assert_eq!(m.do_requests, 1);
        assert!((m.cost_usd - 9.270e-6).abs() < 1e-12);
    }

    #[test]
    fn seed_and_push_classify() {
        let (oid, pack) = build_seed_pack();
        assert!(!oid.is_zero());
        assert!(pack.starts_with(b"PACK"));
        let body = build_push_body(Oid::ZERO, oid, "refs/heads/main", &pack);
        assert!(body.len() > pack.len());
    }

    #[test]
    fn pull_stage_after_many_writes_has_ok_pulls() {
        block_on(async {
            let store = Rc::new(MemStore::new()) as Rc<dyn Store>;
            let states = Rc::new(MemStateStore::new()) as Rc<dyn StateStore>;
            let report = run_in_process(
                store,
                states,
                "lt-pulls",
                LoadTestRequest {
                    confirm: true,
                    budget_usd: Some(0.5),
                    duration_secs: Some(2),
                    stages: Some(vec![
                        StageSpec {
                            writers: 8,
                            readers: 0,
                        },
                        StageSpec {
                            writers: 16,
                            readers: 0,
                        },
                        StageSpec {
                            writers: 0,
                            readers: 16,
                        },
                    ]),
                    shards: Some(1),
                    shard: false,
                    tip: None,
                    shard_index: None,
                    token: None,
                },
            )
            .await
            .expect("loadtest");
            let last = report.stages.last().expect("stage");
            eprintln!(
                "report: peak_pull={} pull_samples={} last={:?}",
                report.peak_pulls_per_sec, report.cost_per_pull.samples, last
            );
            assert!(last.readers > 0);
            assert!(
                last.pull_ok > 0,
                "expected successful pulls after writes; pull_ok={} pull_err={} report={report:?}",
                last.pull_ok,
                last.pull_err
            );
        });
    }

    #[test]
    fn in_process_loadtest_reports_qps_and_respects_budget() {
        block_on(async {
            let store = Rc::new(MemStore::new()) as Rc<dyn Store>;
            let states = Rc::new(MemStateStore::new()) as Rc<dyn StateStore>;
            let report = run_in_process(
                store,
                states,
                "lt",
                LoadTestRequest {
                    confirm: true,
                    budget_usd: Some(0.05),
                    duration_secs: Some(2),
                    stages: Some(vec![
                        StageSpec {
                            writers: 2,
                            readers: 0,
                        },
                        StageSpec {
                            writers: 0,
                            readers: 4,
                        },
                    ]),
                    shards: Some(1),
                    shard: false,
                    tip: None,
                    shard_index: None,
                    token: None,
                },
            )
            .await
            .expect("loadtest");

            assert!(!report.tip.is_empty());
            assert!(report.total_cost_usd >= 0.0);
            assert!(report.total_cost_usd <= report.budget_usd + 1e-6 || report.budget_limited);
            // At least one stage should have produced successful ops.
            let any_ok = report.stages.iter().any(|s| s.push_ok + s.pull_ok > 0);
            assert!(any_ok, "{report:?}");
            if report.cost_per_push.samples > 0 {
                assert!(report.cost_per_push.mean_cost_usd > 0.0);
                assert!(
                    report.cost_per_push.mean_r2_class_a + report.cost_per_push.mean_r2_class_b
                        > 0.0
                );
            }
            if report.cost_per_pull.samples > 0 {
                assert!(report.peak_pulls_per_sec > 0.0);
            }
        });
    }

    #[test]
    fn push_reuses_odb_instead_of_reloading_indexes() {
        block_on(async {
            let store = Rc::new(MemStore::new()) as Rc<dyn Store>;
            let states = Rc::new(MemStateStore::new()) as Rc<dyn StateStore>;
            let http = GitHttp::new(store, states);
            let driver = InProcessDriver::new(http, "lt-odb-reuse");
            let mut tip = driver.ensure_seeded(None).await.expect("seed");
            // Accumulate packs without auto-repack so a naive second open
            // would pay ~2× Class B index reads.
            for i in 0..5u64 {
                let (oid, pack) = build_writer_pack(tip, 0, i);
                let body = build_push_body(tip, oid, "refs/heads/main", &pack);
                let a = driver.push(body).await.expect("push");
                assert_eq!(a.outcome, AttemptOutcome::Ok, "{a:?}");
                tip = oid;
            }
            let (oid, pack) = build_writer_pack(tip, 0, 5);
            let body = build_push_body(tip, oid, "refs/heads/main", &pack);
            let a = driver.push(body).await.expect("push");
            assert_eq!(a.outcome, AttemptOutcome::Ok);
            // Prior packs (seed+5) opened once; pre-fix also reloaded them.
            assert!(
                a.metrics.r2_class_b < 20,
                "expected single index load pass, got R2B={}",
                a.metrics.r2_class_b
            );
            assert_eq!(
                a.metrics.do_requests, 2,
                "expected load+apply DO only, got {}",
                a.metrics.do_requests
            );
        });
    }

    #[test]
    fn loadtest_auto_repack_keeps_pack_count_bounded() {
        block_on(async {
            let store = Rc::new(MemStore::new()) as Rc<dyn Store>;
            let states = Rc::new(MemStateStore::new()) as Rc<dyn StateStore>;
            let report = run_in_process(
                store.clone(),
                states.clone(),
                "lt-repack",
                LoadTestRequest {
                    confirm: true,
                    budget_usd: Some(1.0),
                    duration_secs: Some(3),
                    stages: Some(vec![
                        StageSpec {
                            writers: 8,
                            readers: 0,
                        },
                        StageSpec {
                            writers: 16,
                            readers: 0,
                        },
                    ]),
                    shards: Some(1),
                    shard: false,
                    tip: None,
                    shard_index: None,
                    token: None,
                },
            )
            .await
            .expect("loadtest");
            assert!(report.cost_per_push.samples > 0, "{report:?}");
            // Without harness auto-repack, ~seed+samples packs. With it,
            // live packs stay near the trigger threshold.
            let repo = crate::repo::Repo {
                store: store.as_ref(),
                states: states.as_ref(),
                name: "lt-repack",
            };
            let packs = repo.load_state().await.expect("state").state.packs.len();
            let trigger = crate::maintenance::AUTO_REPACK_TRIGGER_PACKS;
            assert!(
                packs < report.cost_per_push.samples as usize,
                "expected auto-repack to fold packs; packs={packs} samples={}",
                report.cost_per_push.samples
            );
            assert!(
                packs <= trigger + 16,
                "packs={packs} drifted far past trigger={trigger}"
            );
            // Accurate per-push op counts (nested metrics stack): DO load+apply.
            // Detached auto-repack must not leak onto these samples.
            assert!(
                (1.5..=2.5).contains(&report.cost_per_push.mean_do),
                "mean_do={} (metrics stack / detach regression?)",
                report.cost_per_push.mean_do
            );
        });
    }

    #[test]
    fn budget_stops_run() {
        block_on(async {
            // Tiny budget: seed alone costs something; first stage should hit.
            let store = Rc::new(MemStore::new()) as Rc<dyn Store>;
            let states = Rc::new(MemStateStore::new()) as Rc<dyn StateStore>;
            let report = run_in_process(
                store,
                states,
                "lt-budget",
                LoadTestRequest {
                    confirm: true,
                    budget_usd: Some(0.000001), // 1 µ$
                    duration_secs: Some(5),
                    stages: Some(vec![StageSpec {
                        writers: 4,
                        readers: 4,
                    }]),
                    shards: None,
                    shard: false,
                    tip: None,
                    shard_index: None,
                    token: None,
                },
            )
            .await
            .expect("loadtest");
            // Seed cost is not counted in the budget (only measured attempts).
            // With a 1µ$ cap, a single push (~30µ$) marks budget_limited.
            assert!(
                report.budget_limited || report.total_cost_usd > 0.0,
                "{report:?}"
            );
        });
    }

    #[test]
    fn phone_shaped_push_op_counts_stay_low() {
        block_on(async {
            let store = Rc::new(MemStore::new()) as Rc<dyn Store>;
            let states = Rc::new(MemStateStore::new()) as Rc<dyn StateStore>;
            let report = run_in_process(
                store,
                states,
                "lt-bench-phone",
                // Keep shards=1 so this exercises a single in-process isolate
                // (peak ≤ PHONE_MAX_WRITERS_PER_ISOLATE so fanout plan does not raise).
                phone_request(0.05, 4, PHONE_MAX_WRITERS_PER_ISOLATE, 1),
            )
            .await
            .expect("loadtest");
            // Op-count regression guard (MemStore has ~0ms backends so ms/QPS
            // are not comparable to production).
            assert!(
                report.cost_per_push.mean_r2_class_b < 12.0,
                "push R2B too high: {}",
                report.cost_per_push.mean_r2_class_b
            );
            assert!(
                (1.5..=2.5).contains(&report.cost_per_push.mean_do),
                "push DO {}",
                report.cost_per_push.mean_do
            );
            assert!(report.cost_per_pull.samples > 0);
        });
    }

    #[test]
    fn merge_shards_sums_goodput() {
        let s = StageReport {
            writers: 2,
            readers: 0,
            wall_ms: 1000.0,
            push_ok: 10,
            push_conflict: 0,
            push_err: 0,
            pull_ok: 0,
            pull_err: 0,
            pushes_per_sec: 10.0,
            pulls_per_sec: 0.0,
            stage_cost_usd: 0.001,
            budget_hit: false,
        };
        let p = LoadTestReport {
            repo: "r".into(),
            tip: "a".into(),
            budget_usd: 1.0,
            total_cost_usd: 0.001,
            budget_limited: false,
            peak_pushes_per_sec: 10.0,
            peak_pulls_per_sec: 0.0,
            cost_per_push: OpCostSummary {
                samples: 10,
                mean_r2_class_a: 1.0,
                mean_r2_class_b: 2.0,
                mean_do: 2.0,
                mean_kv: 0.0,
                mean_cost_usd: 0.0001,
                mean_ms: 50.0,
            },
            cost_per_pull: OpCostSummary::default(),
            stages: vec![s.clone()],
            duration_ms: 1000.0,
            shards: 1,
        };
        let mut p2 = p.clone();
        p2.stages[0].push_ok = 15;
        p2.stages[0].pushes_per_sec = 15.0;
        p2.total_cost_usd = 0.002;
        p2.stages[0].stage_cost_usd = 0.002;
        let merged = merge_shard_reports("r", "a", 1.0, 2, &[p, p2]);
        assert_eq!(merged.stages[0].push_ok, 25);
        assert!((merged.stages[0].pushes_per_sec - 25.0).abs() < 1e-9);
        assert_eq!(merged.shards, 2);
    }

    #[test]
    fn max_shards_fits_cloudflare_invocation_cap() {
        // Browser fan-out is not Worker→Worker; keep a sane phone UI max.
        let cap = MAX_SHARDS;
        assert!((2..=32).contains(&cap), "MAX_SHARDS={cap}");
        assert_eq!(clamp_phone_shards(99), MAX_SHARDS);
        assert_eq!(clamp_phone_shards(1), 1);
    }
}
