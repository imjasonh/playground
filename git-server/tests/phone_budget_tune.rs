//! Local phone loadtest budget tuner.
//!
//! Run without deploying:
//!
//! ```text
//! cargo test -p git-server --test phone_budget_tune -- --nocapture
//! PHONE_BUDGET_TUNE=1 cargo test -p git-server --test phone_budget_tune tune_search -- --nocapture --ignored
//! ```
//!
//! The default test builds a multi-shard pack backlog, runs peak + readers
//! shard POSTs shaped like production, and fails if subrequests or transient
//! heap exceed the soft caps in `loadtest::PHONE_SHARD_*_SOFT_CAP`.
//!
//! With `PHONE_BUDGET_TUNE=1`, `tune_search` binary-searches safe reader
//! concurrency and prints suggested constants — iterate here instead of
//! redeploying after every Cloudflare 1101.

use futures::executor::block_on;
use git_server::http::GitHttp;
use git_server::loadtest::{
    build_push_body, build_writer_pack, run_in_process, AttemptOutcome, InProcessDriver,
    LoadDriver, LoadTestRequest, StageSpec, PHONE_DEFAULT_DURATION_SECS, PHONE_MAX_OPS_PER_LOOP,
    PHONE_MAX_READERS_PER_ISOLATE, PHONE_MAX_SHARDS, PHONE_MAX_WRITERS_PER_ISOLATE,
    PHONE_SHARD_HEAP_SOFT_CAP, PHONE_SHARD_SUBREQUEST_SOFT_CAP,
};
use git_server::memtrack;
use git_server::object::Oid;
use git_server::refs::{MemStateStore, StateStore};
use git_server::storage::{MemStore, Store};
use std::rc::Rc;

#[global_allocator]
static ALLOC: memtrack::TrackingAllocator = memtrack::TrackingAllocator::new();

#[allow(dead_code)]
struct Scenario {
    name: &'static str,
    writers: u32,
    readers: u32,
    subreqs: u64,
    heap: usize,
    ok_ops: u64,
}

fn mib(n: usize) -> f64 {
    n as f64 / (1024.0 * 1024.0)
}

fn seed_and_backlog(
    store: Rc<dyn Store>,
    states: Rc<dyn StateStore>,
    mem: &MemStore,
    backlog: u64,
) -> String {
    git_server::odb::clear_index_cache_for_test();
    git_server::repo::clear_filelog_cache_for_test();
    let http = GitHttp::new(store.clone(), states.clone());
    let seed = block_on(run_in_process(
        store.clone(),
        states.clone(),
        "lt-tune",
        LoadTestRequest {
            confirm: true,
            budget_usd: Some(0.05),
            duration_secs: Some(1),
            stages: Some(vec![StageSpec {
                writers: 1,
                readers: 0,
            }]),
            shards: Some(1),
            shard: false,
            tip: None,
            shard_index: None,
            token: None,
        },
    ))
    .expect("seed");
    git_server::odb::clear_index_cache_for_test();
    git_server::repo::clear_filelog_cache_for_test();

    let tip = seed.tip.clone();
    let tip_oid = Oid::from_hex(&tip).expect("tip");
    let driver = InProcessDriver::new(http, "lt-tune");
    let mut old = Oid::ZERO;
    let mut tip_commit = tip_oid;
    block_on(async {
        for i in 0..backlog {
            let (oid, pack) = build_writer_pack(tip_commit, 42, i);
            let body = build_push_body(old, oid, "refs/heads/load/backlog", &pack);
            let a = driver.push(body).await.expect("backlog push");
            assert_eq!(a.outcome, AttemptOutcome::Ok, "i={i} {a:?}");
            old = oid;
            tip_commit = oid;
        }
    });
    let _ = mem; // shared via store clone
    tip
}

fn measure_shard(
    name: &'static str,
    store: Rc<dyn Store>,
    states: Rc<dyn StateStore>,
    mem: &MemStore,
    tip: &str,
    writers: u32,
    readers: u32,
) -> Scenario {
    mem.reset_op_counts();
    let live_before = memtrack::live_bytes();
    memtrack::reset_peak();
    let report = block_on(run_in_process(
        store,
        states,
        "lt-tune",
        LoadTestRequest {
            confirm: true,
            budget_usd: Some(1.0),
            duration_secs: Some(PHONE_DEFAULT_DURATION_SECS),
            stages: Some(vec![StageSpec { writers, readers }]),
            shards: Some(1),
            shard: true,
            tip: Some(tip.to_string()),
            shard_index: Some(15),
            token: None,
        },
    ))
    .unwrap_or_else(|e| panic!("{name}: {e}"));
    let ops = mem.op_counts();
    let ok_ops = if writers > 0 {
        report.cost_per_push.samples
    } else {
        report.cost_per_pull.samples
    };
    let do_est = if writers > 0 {
        ok_ops.max(1) * 2
    } else {
        ok_ops.max(1)
    };
    let subreqs = ops.class_a + ops.class_b + do_est;
    let heap = memtrack::peak_delta_since_reset(live_before);
    println!(
        "{name}: writers={writers} readers={readers} ok_ops={ok_ops} \
         subreqs={subreqs} (A={} B={}) heap={:.1} MiB",
        ops.class_a,
        ops.class_b,
        mib(heap)
    );
    Scenario {
        name,
        writers,
        readers,
        subreqs,
        heap,
        ok_ops,
    }
}

#[test]
fn phone_shard_peak_and_readers_under_soft_caps() {
    let backlog = (PHONE_MAX_SHARDS as u64 - 1) * PHONE_MAX_OPS_PER_LOOP as u64;
    let mem = MemStore::new();
    let store = Rc::new(mem.clone()) as Rc<dyn Store>;
    let states = Rc::new(MemStateStore::new()) as Rc<dyn StateStore>;
    let tip = seed_and_backlog(store.clone(), states.clone(), &mem, backlog);

    let peak = measure_shard(
        "peak",
        store.clone(),
        states.clone(),
        &mem,
        &tip,
        PHONE_MAX_WRITERS_PER_ISOLATE,
        0,
    );
    assert!(peak.ok_ops > 0, "peak made no pushes");
    assert!(
        peak.subreqs <= PHONE_SHARD_SUBREQUEST_SOFT_CAP,
        "peak subreqs {} > soft cap {}",
        peak.subreqs,
        PHONE_SHARD_SUBREQUEST_SOFT_CAP
    );
    assert!(
        peak.heap <= PHONE_SHARD_HEAP_SOFT_CAP,
        "peak heap {:.1} MiB > soft cap {:.1} MiB",
        mib(peak.heap),
        mib(PHONE_SHARD_HEAP_SOFT_CAP)
    );

    let readers = measure_shard(
        "readers",
        store,
        states,
        &mem,
        &tip,
        0,
        PHONE_MAX_READERS_PER_ISOLATE,
    );
    assert!(readers.ok_ops > 0, "readers made no pulls");
    assert!(
        readers.subreqs <= PHONE_SHARD_SUBREQUEST_SOFT_CAP,
        "readers subreqs {} > soft cap {}",
        readers.subreqs,
        PHONE_SHARD_SUBREQUEST_SOFT_CAP
    );
    assert!(
        readers.heap <= PHONE_SHARD_HEAP_SOFT_CAP,
        "readers heap {:.1} MiB > soft cap {:.1} MiB",
        mib(readers.heap),
        mib(PHONE_SHARD_HEAP_SOFT_CAP)
    );
}

/// Binary-search how many concurrent readers fit the soft caps on a backlog.
/// Ignored by default; enable with `PHONE_BUDGET_TUNE=1`.
#[test]
#[ignore]
fn tune_search_reader_concurrency() {
    if std::env::var("PHONE_BUDGET_TUNE").ok().as_deref() != Some("1") {
        eprintln!("set PHONE_BUDGET_TUNE=1 to run the tuner");
        return;
    }
    let backlog = (PHONE_MAX_SHARDS as u64 - 1) * PHONE_MAX_OPS_PER_LOOP as u64;
    let mem = MemStore::new();
    let store = Rc::new(mem.clone()) as Rc<dyn Store>;
    let states = Rc::new(MemStateStore::new()) as Rc<dyn StateStore>;
    let tip = seed_and_backlog(store.clone(), states.clone(), &mem, backlog);

    println!("=== phone budget tune (backlog packs ≈ {backlog}) ===");
    let mut best = 0u32;
    for r in 1..=4 {
        let s = measure_shard(
            "tune-readers",
            store.clone(),
            states.clone(),
            &mem,
            &tip,
            0,
            r,
        );
        let ok = s.ok_ops > 0
            && s.subreqs <= PHONE_SHARD_SUBREQUEST_SOFT_CAP
            && s.heap <= PHONE_SHARD_HEAP_SOFT_CAP;
        println!(
            "  readers={r}: {} (subreqs={} heap={:.1} MiB)",
            if ok { "PASS" } else { "FAIL" },
            s.subreqs,
            mib(s.heap)
        );
        if ok {
            best = r;
        } else {
            break;
        }
    }
    println!();
    println!("Suggested PHONE_MAX_READERS_PER_ISOLATE = {best}");
    println!("Current PHONE_MAX_READERS_PER_ISOLATE = {PHONE_MAX_READERS_PER_ISOLATE}");
    assert!(
        best >= PHONE_MAX_READERS_PER_ISOLATE,
        "current reader cap {PHONE_MAX_READERS_PER_ISOLATE} exceeds tuned safe max {best}"
    );
}
