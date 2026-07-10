//! File-log query microbenchmark: monolithic (the pre-sharding layout — one
//! merged `GSFL` segment that every query loads and parses whole) vs
//! path-range sharding (`GSFI` index + ~256 KiB shards; queries load only
//! intersecting shards).
//!
//! Measures the two read-API shapes on a large synthetic history:
//!   * blame:  load scoped to one exact path, then walk its version chain
//!   * tree:   load scoped to a directory prefix, then build the view
//!
//! Run:  cargo bench --bench filelog
//! Env:  FL_PATHS=50000 FL_DIRS=200 FL_VERSIONS=4   (history shape)

use futures::executor::block_on;
use git_server::refs::RepoState;
use git_server::repo::{
    load_filelog_scoped, records_for_path, write_sharded_filelog, Change, FileLogRecord,
    FileLogSegment, FileLogView, FilelogScope,
};
use git_server::storage::{MemStore, Store};
use std::time::Instant;

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

fn synthetic_records(paths: usize, dirs: usize, versions: usize) -> Vec<FileLogRecord> {
    let mut records = Vec::with_capacity(paths * versions);
    // Emit in "chronological" order (all v0s, then v1s…), like merged pushes.
    for v in 0..versions {
        for p in 0..paths {
            let path = format!("dir{:03}/sub{}/file{:06}.txt", p % dirs, p % 7, p);
            records.push(FileLogRecord {
                path,
                commit: format!("{:040x}", v * paths + p + 1),
                time: (v * paths + p) as i64,
                change: if v == 0 { Change::Add } else { Change::Modify },
                blob: format!("{:040x}", v * paths + p + 1_000_000),
                prev_commit: (v > 0).then(|| format!("{:040x}", (v - 1) * paths + p + 1)),
                prev_blob: (v > 0).then(|| format!("{:040x}", (v - 1) * paths + p + 1_000_000)),
            });
        }
    }
    records
}

struct Sample {
    wall_us: f64,
    class_b: u64,
}

fn measure<F: FnMut()>(store: &MemStore, iters: usize, mut f: F) -> Sample {
    f(); // warm up
    store.reset_op_counts();
    let start = Instant::now();
    for _ in 0..iters {
        f();
    }
    let wall_us = start.elapsed().as_secs_f64() * 1e6 / iters as f64;
    let class_b = store.op_counts().class_b / iters as u64;
    Sample { wall_us, class_b }
}

fn main() {
    let paths = env_usize("FL_PATHS", 50_000);
    let dirs = env_usize("FL_DIRS", 200);
    let versions = env_usize("FL_VERSIONS", 4);
    let records = synthetic_records(paths, dirs, versions);
    let total = records.len();
    let bytes = FileLogSegment {
        records: records.clone(),
    }
    .to_bytes()
    .len();
    println!(
        "history: {paths} paths x {versions} versions = {total} records ({:.1} MiB serialized)\n",
        bytes as f64 / (1024.0 * 1024.0)
    );

    let store = MemStore::new();
    let state = |id: &str| RepoState {
        filelog: vec![id.to_string()],
        ..RepoState::empty()
    };

    // Layout A: monolithic merged segment (what maintenance wrote before
    // sharding — every query loads and parses the entire history).
    block_on(
        store.put(
            "r/filelog/mono",
            FileLogSegment {
                records: records.clone(),
            }
            .to_bytes(),
        ),
    )
    .unwrap();
    let mono_state = state("mono");

    // Layout B: path-range shards.
    let shards = block_on(write_sharded_filelog(&store, "r", "sharded", records)).unwrap();
    let sharded_state = state("sharded");
    println!("sharded layout: {shards} shards (~256 KiB target)\n");

    let blame_path = format!("dir{:03}/sub{}/file{:06}.txt", 4242 % dirs, 4242 % 7, 4242);
    let tree_prefix = "dir042/";

    let blame = |st: &RepoState, scope: FilelogScope| {
        let segs = block_on(load_filelog_scoped(&store, "r", st, &scope)).unwrap();
        let chain = records_for_path(&segs, &blame_path);
        assert_eq!(chain.len(), versions);
    };
    let tree = |st: &RepoState, scope: FilelogScope| {
        let segs = block_on(load_filelog_scoped(&store, "r", st, &scope)).unwrap();
        let view = FileLogView::new(&segs);
        assert!(view.latest_for_prefix(tree_prefix).is_some());
    };

    println!("{:<44} {:>12} {:>12}", "query", "wall/query", "R2 classB");
    let report = |name: &str, s: &Sample| {
        println!("{:<44} {:>10.1}µs {:>12}", name, s.wall_us, s.class_b);
    };

    let s = measure(&store, 5, || {
        blame(&mono_state, FilelogScope::Path(&blame_path))
    });
    report("blame chain  | monolithic (before)", &s);
    let s = measure(&store, 50, || {
        blame(&sharded_state, FilelogScope::Path(&blame_path))
    });
    report("blame chain  | sharded (after)", &s);

    let s = measure(&store, 5, || {
        tree(&mono_state, FilelogScope::Prefix(tree_prefix))
    });
    report("dir listing  | monolithic (before)", &s);
    let s = measure(&store, 50, || {
        tree(&sharded_state, FilelogScope::Prefix(tree_prefix))
    });
    report("dir listing  | sharded (after)", &s);

    // Root listing is the worst case for sharding (prefix "" intersects every
    // shard); report it honestly.
    let s = measure(&store, 5, || tree(&mono_state, FilelogScope::Prefix("")));
    report("root listing | monolithic (before)", &s);
    let s = measure(&store, 5, || tree(&sharded_state, FilelogScope::Prefix("")));
    report("root listing | sharded (after, worst case)", &s);
}
