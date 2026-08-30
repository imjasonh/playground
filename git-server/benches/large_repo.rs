//! Large-repo end-to-end benchmark: a real `git` client pushing, cloning, and
//! pulling a big synthetic repository through the native server (in-memory
//! storage), with per-phase timing and backend-op counts to expose hotspots.
//!
//! Run:  cargo bench --bench large_repo
//! Env:  LR_COMMITS=200 LR_FILES=2000 LR_DIRS=50  (override repo shape)
//!
//! The repo shape defaults to ~2k files across ~50 directories with 200
//! commits touching random subsets — large enough that quadratic behavior or
//! per-object overheads dominate and show up clearly in the phase report.

use git_server::http::{GitHttp, Request as GitRequest};
use git_server::storage::MemStore;
use git_server::testutil::{deterministic_noise, env_usize, git, ReaderBody, TestServer};
use std::time::{Duration, Instant};

struct BenchPhase {
    name: &'static str,
    wall: Duration,
    class_a: u64,
    class_b: u64,
    do_ops: u64,
    /// Pack bytes moved (push: received; clone/pull: sent). 0 for APIs.
    bytes: u64,
}

impl BenchPhase {
    /// Marginal request cost (shared model: [`git_server::metrics::cost`]).
    /// KV is a production-only concern, so it's 0 here.
    fn cost_usd(&self) -> f64 {
        git_server::metrics::cost::marginal_usd(self.class_a, self.class_b, self.do_ops, 0)
    }
}

fn main() {
    let commits = env_usize("LR_COMMITS", 200);
    let files = env_usize("LR_FILES", 2_000);
    let dirs = env_usize("LR_DIRS", 50);
    // Optional bulk payload: LR_BLOB_MB adds that many MiB of incompressible
    // binary in the initial commit, so push/pull GiB/s reflects bulk byte
    // movement rather than many-tiny-object overhead.
    let blob_mb = env_usize("LR_BLOB_MB", 0);

    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();

    // --- Generate the synthetic repo locally (not timed as a server phase).
    println!("generating synthetic repo: {commits} commits, {files} files, {dirs} dirs …");
    let gen_start = Instant::now();
    git(&src, &["init", "-q", "-b", "main", "."]);
    let mut rng = 0x243f6a8885a308d3u64;
    let mut rand = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    // Initial commit: all files.
    for f in 0..files {
        let dir = src.join(format!("dir{:02}", f % dirs));
        std::fs::create_dir_all(&dir).unwrap();
        let mut content = String::with_capacity(2048);
        for line in 0..40 {
            content.push_str(&format!("file {f} line {line} :: {}\n", rand() % 100000));
        }
        std::fs::write(dir.join(format!("file{f}.txt")), content).unwrap();
    }
    if blob_mb > 0 {
        let data = deterministic_noise(blob_mb * 1024 * 1024, 0x9e3779b97f4a7c15);
        std::fs::write(src.join("bulk.bin"), &data).unwrap();
    }
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "initial import"]);
    // History: each commit touches a random ~1% of files. Stage only the
    // touched paths (a full `git add .` rescan per commit dominates
    // generation time otherwise).
    for c in 1..commits {
        let touches = (files / 100).max(1);
        let mut touched: Vec<String> = Vec::with_capacity(touches);
        for _ in 0..touches {
            let f = (rand() as usize) % files;
            let rel = format!("dir{:02}/file{f}.txt", f % dirs);
            let path = src.join(&rel);
            let mut content = std::fs::read_to_string(&path).unwrap();
            content.push_str(&format!("edited in commit {c} :: {}\n", rand() % 100000));
            std::fs::write(&path, content).unwrap();
            touched.push(rel);
        }
        let mut args: Vec<&str> = vec!["add", "--"];
        args.extend(touched.iter().map(|s| s.as_str()));
        git(&src, &args);
        git(&src, &["commit", "-q", "-m", &format!("commit {c}")]);
    }
    println!("generated in {:.1?}", gen_start.elapsed());

    let server = TestServer::start();
    let (store, states) = (server.store.clone(), server.states.clone());
    let url = server.url("bench");
    git(&src, &["remote", "add", "origin", &url]);

    let stored_pack_bytes = |store: &MemStore| -> u64 {
        store
            .keys()
            .iter()
            .filter(|k| k.ends_with(".pack"))
            .map(|k| {
                futures::executor::block_on(git_server::storage::Store::size(store, k))
                    .unwrap()
                    .unwrap_or(0)
            })
            .sum()
    };

    let phases: std::cell::RefCell<Vec<BenchPhase>> = std::cell::RefCell::new(Vec::new());
    let run_phase = |name: &'static str, bytes: u64, f: &mut dyn FnMut()| {
        store.reset_op_counts();
        states.reset_op_count();
        let start = Instant::now();
        f();
        let wall = start.elapsed();
        let ops = store.op_counts();
        phases.borrow_mut().push(BenchPhase {
            name,
            wall,
            class_a: ops.class_a,
            class_b: ops.class_b,
            do_ops: states.op_count(),
            bytes,
        });
    };

    // --- Phases -------------------------------------------------------------
    run_phase("push (full history)", 0, &mut || {
        git(&src, &["push", "-q", "origin", "main"]);
    });
    let full_pack_bytes = stored_pack_bytes(&store);
    phases.borrow_mut().last_mut().unwrap().bytes = full_pack_bytes;

    let clone1 = tmp.path().join("clone1");
    run_phase("clone (full)", full_pack_bytes, &mut || {
        git(tmp.path(), &["clone", "-q", &url, clone1.to_str().unwrap()]);
    });

    // Incremental: 5 more commits, push, then pull into the clone.
    for c in 0..5 {
        let path = src.join("dir00/file0.txt");
        let mut content = std::fs::read_to_string(&path).unwrap();
        content.push_str(&format!("incremental {c}\n"));
        std::fs::write(&path, content).unwrap();
        git(&src, &["add", "."]);
        git(&src, &["commit", "-q", "-m", &format!("inc {c}")]);
    }
    run_phase("push (incremental, 5 commits)", 0, &mut || {
        git(&src, &["push", "-q", "origin", "main"]);
    });
    let inc_pack_bytes = stored_pack_bytes(&store) - full_pack_bytes;
    phases.borrow_mut().last_mut().unwrap().bytes = inc_pack_bytes;

    run_phase("pull (incremental)", inc_pack_bytes, &mut || {
        git(&clone1, &["pull", "-q", "origin", "main"]);
    });

    // Read APIs straight through the router (no HTTP client noise).
    let api = |path: String| {
        let git = GitHttp::new(
            std::rc::Rc::new(store.clone()),
            std::rc::Rc::new(states.clone()),
        );
        let req = GitRequest {
            method: "GET",
            path: &path,
            query: None,
            git_protocol: None,
            content_encoding: None,
            cf_ray: None,
        };
        let mut body = ReaderBody::new(std::io::empty());
        let resp = futures::executor::block_on(git.handle(&req, &mut body, "api"));
        let status = resp.status;
        let body = futures::executor::block_on(resp.body.into_bytes()).unwrap();
        assert_eq!(status, 200, "{path}: {}", String::from_utf8_lossy(&body));
        body.len()
    };
    run_phase("file API (1 file)", 0, &mut || {
        api("/api/bench/file/main/dir00/file0.txt".to_string());
    });
    run_phase("tree API (1 dir)", 0, &mut || {
        api("/api/bench/tree/main/dir00".to_string());
    });
    run_phase("blame API (hot file)", 0, &mut || {
        api("/api/bench/blame/main/dir00/file0.txt".to_string());
    });

    run_phase("repack", 0, &mut || {
        let git = GitHttp::new(
            std::rc::Rc::new(store.clone()),
            std::rc::Rc::new(states.clone()),
        );
        let req = GitRequest {
            method: "POST",
            path: "/api/bench/repack",
            query: None,
            git_protocol: None,
            content_encoding: None,
            cf_ray: None,
        };
        let mut body = ReaderBody::new(std::io::empty());
        let resp = futures::executor::block_on(git.handle(&req, &mut body, "repack"));
        assert_eq!(resp.status, 200);
        let body = futures::executor::block_on(resp.body.into_bytes()).unwrap();
        assert!(String::from_utf8_lossy(&body).contains("Repacked"));
    });

    let repacked_bytes = stored_pack_bytes(&store);
    let clone2 = tmp.path().join("clone2");
    run_phase("clone (after repack)", repacked_bytes, &mut || {
        git(tmp.path(), &["clone", "-q", &url, clone2.to_str().unwrap()]);
    });
    run_phase("blame API (after repack)", 0, &mut || {
        api("/api/bench/blame/main/dir00/file0.txt".to_string());
    });

    // --- Report ---------------------------------------------------------------
    let stored: u64 = store
        .keys()
        .iter()
        .map(|k| {
            futures::executor::block_on(git_server::storage::Store::size(&store, k))
                .unwrap()
                .unwrap_or(0)
        })
        .sum();
    println!();
    println!(
        "repo: {commits} commits, {files} files; stored bytes: {:.1} MiB",
        stored as f64 / (1024.0 * 1024.0)
    );
    println!(
        "{:<32} {:>11} {:>9} {:>9} {:>4} {:>10} {:>12}",
        "phase", "wall", "classA", "classB", "DO", "thru", "op cost"
    );
    let phases = phases.into_inner();
    for p in &phases {
        let thru = if p.bytes > 0 {
            let gib_s = p.bytes as f64 / (1024.0 * 1024.0 * 1024.0) / p.wall.as_secs_f64();
            if gib_s >= 0.01 {
                format!("{gib_s:.2} GiB/s")
            } else {
                format!("{:.1} MiB/s", gib_s * 1024.0)
            }
        } else {
            "-".to_string()
        };
        println!(
            "{:<32} {:>11.2?} {:>9} {:>9} {:>4} {:>10} {:>10.3}µ$",
            p.name,
            p.wall,
            p.class_a,
            p.class_b,
            p.do_ops,
            thru,
            p.cost_usd() * 1e6,
        );
    }

    // Marginal $ per GiB moved (R2/DO request costs only; egress is free and
    // Worker request+CPU costs are covered in docs/design.md). Only phases
    // moving enough data for per-GiB extrapolation to be meaningful: tiny
    // transfers are dominated by fixed per-request costs (see the per-op
    // column above for those).
    println!();
    for p in &phases {
        if p.bytes < 8 * 1024 * 1024 {
            continue;
        }
        let gib = p.bytes as f64 / (1024.0 * 1024.0 * 1024.0);
        println!(
            "{:<32} {:>10.2} MiB moved -> {:>8.2} µ$/GiB (request costs)",
            p.name,
            p.bytes as f64 / (1024.0 * 1024.0),
            p.cost_usd() / gib * 1e6,
        );
    }
}
