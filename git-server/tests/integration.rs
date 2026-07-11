//! End-to-end integration tests: a real `git` client (clone/push/pull/tags)
//! against the same handler code the Worker runs, plus the read APIs and
//! repacking, with cost-model assertions along the way.
//!
//! Requires `git` on PATH (present in CI and dev machines).

mod common;

use common::{deterministic_noise, git, git_try, write_file, TestServer};
use serde_json::Value;
use std::path::Path;
use std::process::Command;

/// True when `oid` is not present as a real local object (promisor placeholders
/// do not count). Partial-clone clients still answer `cat-file -e` for promised
/// oids, so we must inspect `--batch-all-objects` instead.
fn local_object_missing(dir: &Path, oid: &str) -> bool {
    let out = Command::new("git")
        .args(["cat-file", "--batch-check", "--batch-all-objects"])
        .current_dir(dir)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("HOME", dir)
        .output()
        .expect("git cat-file");
    assert!(out.status.success(), "batch-all-objects failed");
    let text = String::from_utf8_lossy(&out.stdout);
    !text.lines().any(|l| l.starts_with(oid))
}

/// The repo status API: EMPTY before any push, READY after, with default
/// branch, head commit, size counters, and a last-push timestamp.
#[test]
fn status_api() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();

    // Unknown/never-pushed repo reports EMPTY.
    let (status, body) = server.get("/api/proj");
    assert_eq!(status, 200);
    let s: Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(s["status"], "EMPTY");
    assert_eq!(s["objects"], 0);
    assert!(s["last_push_ms"].is_null());

    // Push something.
    git(&src, &["init", "-q", "-b", "main", "."]);
    write_file(&src, "a.txt", "hello\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "first"]);
    git(&src, &["remote", "add", "origin", &server.url("proj")]);
    git(&src, &["push", "-q", "origin", "main"]);
    let head = git(&src, &["rev-parse", "HEAD"]).trim().to_string();

    let (status, body) = server.get("/api/proj");
    assert_eq!(status, 200);
    let s: Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(s["status"], "READY");
    assert_eq!(s["default_branch"], "main");
    assert_eq!(s["head"], "refs/heads/main");
    assert_eq!(s["head_commit"].as_str().unwrap(), head);
    assert!(s["objects"].as_u64().unwrap() >= 3); // commit + tree + blob
    assert!(s["bytes"].as_u64().unwrap() > 0);
    assert!(
        s["last_push_ms"].as_i64().is_some(),
        "last_push recorded: {s}"
    );
}

/// Full lifecycle: push to empty repo, clone it back, incremental push+pull,
/// read APIs, blame vs `git blame`, repack, and re-verify everything.
#[test]
fn end_to_end() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();

    // --- 1. Create a repo locally and push it. -----------------------------
    git(&src, &["init", "-q", "-b", "main", "."]);
    write_file(&src, "README.md", "# hello\n\nworld\n");
    write_file(&src, "src/lib.rs", "fn one() {}\nfn two() {}\n");
    write_file(&src, "src/deep/nested/mod.rs", "pub mod deep;\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "initial commit"]);
    git(&src, &["remote", "add", "origin", &server.url("test.git")]);

    server.store.reset_op_counts();
    git(&src, &["push", "-q", "origin", "main"]);
    let push_ops = server.store.op_counts();
    println!("push ops: {push_ops:?}");

    // --- 2. Clone it back and verify. ---------------------------------------
    let clone1 = tmp.path().join("clone1");
    server.store.reset_op_counts();
    git(
        tmp.path(),
        &["clone", "-q", &server.url("test.git"), "clone1"],
    );
    let clone_ops = server.store.op_counts();
    println!("clone ops: {clone_ops:?}");
    assert_eq!(
        std::fs::read_to_string(clone1.join("README.md")).unwrap(),
        "# hello\n\nworld\n"
    );
    git(&clone1, &["fsck", "--strict"]);

    // A fresh clone of a single-pack repo should cost O(1) backend reads,
    // not O(objects): state doc + index + ranged reads for entry payloads.
    // (MemStore counts every get_range; the Worker batches per object.)
    assert!(
        clone_ops.class_a < 5,
        "clone should not write: {clone_ops:?}"
    );

    // --- 3. Incremental push, then incremental pull. ------------------------
    write_file(
        &src,
        "src/lib.rs",
        "fn one() {}\nfn two() {}\nfn three() {}\n",
    );
    write_file(&src, "docs/guide.md", "guide\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "add three and guide"]);
    git(&src, &["push", "-q", "origin", "main"]);

    git(&clone1, &["pull", "-q", "origin", "main"]);
    assert_eq!(
        std::fs::read_to_string(clone1.join("docs/guide.md")).unwrap(),
        "guide\n"
    );
    git(&clone1, &["fsck", "--strict"]);

    // --- 4. Read APIs. -------------------------------------------------------
    let (status, body) = server.get("/api/test/file/main/src/lib.rs");
    assert_eq!(status, 200);
    assert_eq!(
        String::from_utf8_lossy(&body),
        "fn one() {}\nfn two() {}\nfn three() {}\n"
    );

    let (status, body) = server.get("/api/test/file/main/no/such/file");
    assert_eq!(status, 404, "{}", String::from_utf8_lossy(&body));

    let (status, body) = server.get("/api/test/tree/main/src");
    assert_eq!(status, 200);
    let tree: Value = serde_json::from_slice(&body).unwrap();
    let entries = tree["entries"].as_array().unwrap();
    let names: Vec<&str> = entries
        .iter()
        .map(|e| e["name"].as_str().unwrap())
        .collect();
    assert!(names.contains(&"lib.rs"));
    assert!(names.contains(&"deep"));
    let lib = entries.iter().find(|e| e["name"] == "lib.rs").unwrap();
    // lib.rs was modified by the second push: its last_commit must be the
    // second commit — consistent immediately after the push.
    let head = git(&src, &["rev-parse", "HEAD"]).trim().to_string();
    assert_eq!(lib["last_commit"].as_str().unwrap(), head);

    let (status, body) = server.get("/api/test/refs");
    assert_eq!(status, 200);
    let refs: Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(refs["refs"]["refs/heads/main"].as_str().unwrap(), head);

    // Observability: every response carries a Server-Timing header with the
    // cost-model op counters and phase timings.
    let (status, headers, _) = server.get_with_headers("/api/test/blame/main/src/lib.rs");
    assert_eq!(status, 200);
    let timing = headers
        .lines()
        .find(|l| l.to_ascii_lowercase().starts_with("server-timing:"))
        .expect("Server-Timing header present");
    assert!(timing.contains("total;dur="), "{timing}");
    assert!(timing.contains("r2b;desc="), "{timing}");
    assert!(timing.contains("do;desc=\"1\""), "{timing}");
    assert!(timing.contains("cost;desc="), "{timing}");

    // --- 5. Blame matches git blame. ----------------------------------------
    assert_blame_matches(&server, &src, "src/lib.rs");

    // --- 6. Repack, then verify everything still works. ----------------------
    let packs_before = server
        .store
        .keys()
        .iter()
        .filter(|k| k.ends_with(".pack"))
        .count();
    assert!(packs_before >= 2, "expected multiple packs before repack");

    let (status, body) = server.post("/api/test/repack");
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&body));
    let result: Value = serde_json::from_slice(&body).unwrap();
    assert!(result["result"].as_str().unwrap().contains("Repacked"));

    // The manifest now names a single pack. Superseded pack *storage* is
    // deliberately still present (deferred deletion: retired ids are swept
    // only after the grace period, so in-flight readers never lose data).
    let status_after: Value = serde_json::from_slice(&server.get("/api/test").1).unwrap();
    assert_eq!(status_after["packs"], 1, "one manifest pack after repack");
    let stored_packs = server
        .store
        .keys()
        .iter()
        .filter(|k| k.ends_with(".pack"))
        .count();
    assert_eq!(
        stored_packs,
        packs_before + 1,
        "superseded packs retained for the grace period"
    );

    // A fresh clone from the consolidated pack must still fsck cleanly.
    git(
        tmp.path(),
        &["clone", "-q", &server.url("test.git"), "clone2"],
    );
    git(&tmp.path().join("clone2"), &["fsck", "--strict"]);
    assert_eq!(
        std::fs::read_to_string(tmp.path().join("clone2/docs/guide.md")).unwrap(),
        "guide\n"
    );

    // Blame still works after segments were merged.
    assert_blame_matches(&server, &src, "src/lib.rs");
}

/// Blame across several modifying commits, verified line-by-line against
/// `git blame`.
#[test]
fn blame_multi_commit_history() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("blamed")]);

    write_file(&src, "poem.txt", "roses are red\nviolets are blue\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "c1"]);

    write_file(
        &src,
        "poem.txt",
        "roses are red\nviolets are blue\nsugar is sweet\n",
    );
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "c2"]);

    write_file(
        &src,
        "poem.txt",
        "roses are crimson\nviolets are blue\nsugar is sweet\nand so are you\n",
    );
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "c3"]);

    // Three separate pushes: exercises the file-log prev-pointer chain across
    // segments.
    git(&src, &["push", "-q", "origin", "HEAD~2:refs/heads/main"]);
    git(&src, &["push", "-q", "origin", "HEAD~1:refs/heads/main"]);
    git(&src, &["push", "-q", "origin", "main"]);

    assert_blame_matches(&server, &src, "poem.txt");
}

/// Branches, deletes, and annotated tags.
#[test]
fn branches_tags_and_deletes() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("multi")]);
    write_file(&src, "a.txt", "a\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "base"]);
    git(&src, &["push", "-q", "origin", "main"]);

    // Feature branch.
    git(&src, &["checkout", "-q", "-b", "feature"]);
    write_file(&src, "b.txt", "b\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "feature work"]);
    git(&src, &["push", "-q", "origin", "feature"]);

    // Annotated tag.
    git(&src, &["tag", "-a", "v1.0", "-m", "release v1.0"]);
    git(&src, &["push", "-q", "origin", "v1.0"]);

    // Clone sees everything.
    git(tmp.path(), &["clone", "-q", &server.url("multi"), "clone"]);
    let clone = tmp.path().join("clone");
    let branches = git(&clone, &["branch", "-r"]);
    assert!(branches.contains("origin/feature"), "{branches}");
    let tags = git(&clone, &["tag", "-l"]);
    assert!(tags.contains("v1.0"), "{tags}");
    git(&clone, &["fsck", "--strict"]);

    // Delete the branch on the remote.
    git(&src, &["push", "-q", "origin", ":refs/heads/feature"]);
    let (status, body) = server.get("/api/multi/refs");
    assert_eq!(status, 200);
    let refs: Value = serde_json::from_slice(&body).unwrap();
    assert!(refs["refs"]["refs/heads/feature"].is_null());
    assert!(refs["refs"]["refs/tags/v1.0"].is_string());
}

/// Non-fast-forward pushes are rejected with a proper report-status (client
/// sees "fetch first" and exits non-zero), and the ref is unchanged.
#[test]
fn rejects_non_fast_forward() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let a = tmp.path().join("a");
    let b = tmp.path().join("b");
    std::fs::create_dir(&a).unwrap();
    git(&a, &["init", "-q", "-b", "main", "."]);
    git(&a, &["remote", "add", "origin", &server.url("race")]);
    write_file(&a, "f.txt", "1\n");
    git(&a, &["add", "."]);
    git(&a, &["commit", "-q", "-m", "one"]);
    git(&a, &["push", "-q", "origin", "main"]);
    let first = git(&a, &["rev-parse", "HEAD"]).trim().to_string();

    // Second client clones, then both try to advance the same ref.
    git(tmp.path(), &["clone", "-q", &server.url("race"), "b"]);
    write_file(&a, "f.txt", "1\n2\n");
    git(&a, &["add", "."]);
    git(&a, &["commit", "-q", "-m", "two-from-a"]);
    git(&a, &["push", "-q", "origin", "main"]);

    write_file(&b, "f.txt", "conflicting\n");
    git(&b, &["add", "."]);
    git(&b, &["commit", "-q", "-m", "two-from-b"]);
    let (ok, output) = git_try(&b, &["push", "-q", "origin", "main"]);
    assert!(!ok, "non-ff push should fail: {output}");

    // Ref advanced only to a's commit.
    let (_, body) = server.get("/api/race/refs");
    let refs: Value = serde_json::from_slice(&body).unwrap();
    let head = refs["refs"]["refs/heads/main"].as_str().unwrap();
    assert_ne!(head, first);
    let a_head = git(&a, &["rev-parse", "HEAD"]).trim().to_string();
    assert_eq!(head, a_head);
}

/// Truly concurrent pushes — both prepared against the same (now stale)
/// state snapshot, simulating temporal overlap the sequential test server
/// can't produce — land when they touch disjoint refs, because the state
/// store merges per-ref deltas instead of CASing the whole document. A
/// same-ref race still fails per-ref with "fetch first".
#[test]
fn concurrent_disjoint_pushes_both_land() {
    use futures::executor::block_on;
    use git_server::object::Oid;
    use git_server::repo::{RefUpdate, Repo};

    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("conc")]);
    write_file(&src, "f.txt", "1\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "one"]);
    git(&src, &["push", "-q", "origin", "main"]);
    let tip = Oid::from_hex(git(&src, &["rev-parse", "HEAD"]).trim()).unwrap();

    let repo = Repo {
        store: &server.store,
        states: &server.states,
        name: "conc",
    };
    // Both "pushes" load the same snapshot before either applies — the
    // interleaving that made the old whole-document CAS reject the loser.
    let (snapshot, _) = block_on(repo.load_state()).unwrap();

    let create = |name: &str| {
        vec![RefUpdate {
            name: name.to_string(),
            old: Oid::ZERO,
            new: tip,
        }]
    };
    let out_a =
        block_on(repo.apply_push(create("refs/heads/a"), None, snapshot.clone(), 1)).unwrap();
    let out_b =
        block_on(repo.apply_push(create("refs/heads/b"), None, snapshot.clone(), 2)).unwrap();
    assert!(out_a.applied && out_a.results[0].error.is_none());
    assert!(
        out_b.applied && out_b.results[0].error.is_none(),
        "disjoint-ref push from a stale snapshot must land: {:?}",
        out_b.results[0].error
    );

    // A same-ref race (still claiming the ref is absent) loses, per-ref.
    let out_c = block_on(repo.apply_push(create("refs/heads/a"), None, snapshot, 3)).unwrap();
    assert!(!out_c.applied);
    assert_eq!(out_c.results[0].error.as_deref(), Some("fetch first"));

    // Both branches are visible and cloneable.
    let (_, body) = server.get("/api/conc/refs");
    let refs: Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(refs["refs"]["refs/heads/a"], tip.to_hex());
    assert_eq!(refs["refs"]["refs/heads/b"], tip.to_hex());
    git(tmp.path(), &["clone", "-q", &server.url("conc"), "check"]);
    git(&tmp.path().join("check"), &["fsck", "--strict"]);
}

/// Incremental repack: with a pack-count budget smaller than the backlog,
/// each run folds only a bounded selection (leaving the rest), repeated runs
/// converge to a single pack, and the repo stays fully readable throughout.
#[test]
fn incremental_repack_converges_within_budget() {
    use futures::executor::block_on;
    use git_server::maintenance::{repack_with_budget, RepackBudget, RepackOutcome};
    use git_server::refs::StateStore;
    use git_server::repo::Repo;

    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("inc")]);
    for i in 1..=7 {
        write_file(&src, "f.txt", &format!("{i}\n"));
        write_file(&src, &format!("dir/g{i}.txt"), "x\n");
        git(&src, &["add", "."]);
        git(&src, &["commit", "-q", "-m", &format!("c{i}")]);
        git(&src, &["push", "-q", "origin", "main"]);
    }
    let status: Value = serde_json::from_slice(&server.get("/api/inc").1).unwrap();
    assert_eq!(status["packs"], 7);

    let repo = Repo {
        store: &server.store,
        states: &server.states,
        name: "inc",
    };
    // grace_ms: 0 — no concurrent readers here, so sweep retired storage on
    // the next run (exercises the deferred-deletion path end-to-end).
    let budget = RepackBudget {
        max_packs: 3,
        grace_ms: 0,
        ..Default::default()
    };

    // A held maintenance lease makes a run skip as Busy, without work.
    let now = git_server::metrics::now_ms() as i64;
    assert!(block_on(server.states.repack_lease("inc", now, 60_000)).unwrap());
    assert_eq!(
        block_on(repack_with_budget(&repo, "held", &budget)).unwrap(),
        RepackOutcome::Busy
    );
    block_on(server.states.repack_unlease("inc")).unwrap();

    // First run folds exactly the budgeted number of packs, not everything.
    match block_on(repack_with_budget(&repo, "r0", &budget)).unwrap() {
        RepackOutcome::Repacked {
            packs, remaining, ..
        } => {
            assert_eq!(packs, 3);
            assert_eq!(remaining, 4);
        }
        other => panic!("expected bounded consolidation, got {other:?}"),
    }
    // The partially-consolidated repo is fully readable.
    let (s, body) = server.get("/api/inc/blame/main/f.txt");
    assert_eq!(s, 200, "{}", String::from_utf8_lossy(&body));

    // Repeated bounded runs converge to a single pack.
    let mut runs = 0;
    loop {
        match block_on(repack_with_budget(
            &repo,
            &format!("r{}", runs + 1),
            &budget,
        ))
        .unwrap()
        {
            RepackOutcome::NoOp => break,
            RepackOutcome::Repacked { packs, .. } => assert!(packs <= 3),
            other => panic!("unexpected {other:?}"),
        }
        runs += 1;
        assert!(runs < 10, "repack failed to converge");
    }
    let status: Value = serde_json::from_slice(&server.get("/api/inc").1).unwrap();
    assert_eq!(status["packs"], 1, "converged to a single pack");
    // The final NoOp run swept all previously-retired ids (grace 0), so
    // nothing superseded lingers in the manifest.
    let (final_state, _) = block_on(repo.load_state()).unwrap();
    assert!(
        final_state.retired.is_empty(),
        "retired not swept: {:?}",
        final_state.retired
    );

    // Everything still clones, fscks, and blames correctly.
    git(
        tmp.path(),
        &["clone", "-q", &server.url("inc"), "inc-check"],
    );
    let d = tmp.path().join("inc-check");
    git(&d, &["fsck", "--strict"]);
    assert_eq!(git(&d, &["rev-list", "--count", "HEAD"]).trim(), "7");
    assert_eq!(std::fs::read_to_string(d.join("f.txt")).unwrap(), "7\n");
    let (s, body) = server.get("/api/inc/blame/main/f.txt");
    assert_eq!(s, 200);
    let blame: Value = serde_json::from_slice(&body).unwrap();
    assert!(blame["lines"].as_array().is_some());
}

/// Pushes over the size limit are rejected — mirroring Cloudflare's
/// request-body cap (~100 MB), which in production 413s over-limit pushes at
/// the edge before the Worker runs. Enforcing (a shrunken) limit locally
/// keeps the harness honest about production behavior, per docs/design.md
/// "Size limits".
#[test]
fn rejects_push_over_size_limit() {
    let server = TestServer::start_with_push_limit(256 * 1024);
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("capped")]);

    // A small push under the limit succeeds…
    write_file(&src, "ok.txt", "fine\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "small"]);
    git(&src, &["push", "-q", "origin", "main"]);

    // …but an incompressible 1 MiB blob blows the 256 KiB limit.
    let data = deterministic_noise(1024 * 1024, 0x2545f4914f6cdd1d);
    std::fs::write(src.join("big.bin"), &data).unwrap();
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "too big"]);
    let (ok, output) = git_try(&src, &["push", "origin", "main"]);
    assert!(!ok, "over-limit push must fail: {output}");
    assert!(
        output.contains("per-push limit"),
        "client should see the limit message with the split-push hint: {output}"
    );

    // The refused push left no trace: the ref still points at the small
    // commit, and no staged pack was published.
    let (_, body) = server.get("/api/capped/refs");
    let refs: serde_json::Value = serde_json::from_slice(&body).unwrap();
    let head = refs["refs"]["refs/heads/main"].as_str().unwrap();
    let small = git(&src, &["rev-parse", "HEAD~1"]).trim().to_string();
    assert_eq!(head, small, "ref must still point at the pre-limit commit");
}

/// Shallow clone (`--depth`) and deepening, driven by a real `git` client.
#[test]
fn shallow_clone_and_deepen() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("shallow")]);

    // Five commits so depth actually truncates history.
    for i in 1..=5 {
        write_file(&src, "f.txt", &format!("line {i}\n"));
        git(&src, &["add", "."]);
        git(&src, &["commit", "-q", "-m", &format!("c{i}")]);
    }
    git(&src, &["push", "-q", "origin", "main"]);
    let tip = git(&src, &["rev-parse", "HEAD"]).trim().to_string();

    // --depth 1: exactly one commit, correct tip content, fsck-clean.
    let d1 = tmp.path().join("d1");
    git(
        tmp.path(),
        &["clone", "-q", "--depth", "1", &server.url("shallow"), "d1"],
    );
    git(&d1, &["fsck", "--strict"]);
    let count = git(&d1, &["rev-list", "--count", "HEAD"]);
    assert_eq!(count.trim(), "1", "depth-1 clone has one commit");
    assert_eq!(git(&d1, &["rev-parse", "HEAD"]).trim(), tip);
    assert_eq!(
        std::fs::read_to_string(d1.join("f.txt")).unwrap(),
        "line 5\n"
    );
    assert!(d1.join(".git/shallow").exists(), "clone is marked shallow");

    // --depth 3: three commits.
    let d3 = tmp.path().join("d3");
    git(
        tmp.path(),
        &["clone", "-q", "--depth", "3", &server.url("shallow"), "d3"],
    );
    git(&d3, &["fsck", "--strict"]);
    assert_eq!(git(&d3, &["rev-list", "--count", "HEAD"]).trim(), "3");

    // Deepen the depth-1 clone to full history.
    git(&d1, &["fetch", "-q", "--unshallow", "origin"]);
    git(&d1, &["fsck", "--strict"]);
    assert_eq!(
        git(&d1, &["rev-list", "--count", "HEAD"]).trim(),
        "5",
        "unshallow recovers full history"
    );
}

/// Partial clone (`--filter=blob:none`): the initial pack omits blobs; a
/// follow-up fetch (checkout / lazy promisor fetch) brings them in.
#[test]
fn partial_clone_blob_none_then_fetch_blobs() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("partial")]);

    write_file(&src, "readme.txt", "hello partial\n");
    write_file(&src, "dir/nested.txt", "nested content\n");
    // A second commit so history isn't trivial.
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "first"]);
    write_file(&src, "readme.txt", "hello partial v2\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "second"]);
    git(&src, &["push", "-q", "origin", "main"]);

    let readme_blob = git(&src, &["rev-parse", "HEAD:readme.txt"])
        .trim()
        .to_string();
    let nested_blob = git(&src, &["rev-parse", "HEAD:dir/nested.txt"])
        .trim()
        .to_string();
    let tree = git(&src, &["rev-parse", "HEAD^{tree}"]).trim().to_string();
    let tip = git(&src, &["rev-parse", "HEAD"]).trim().to_string();

    // --no-checkout: clone must not lazy-fetch blobs for a working tree yet.
    git(
        tmp.path(),
        &[
            "clone",
            "-q",
            "--filter=blob:none",
            "--no-checkout",
            &server.url("partial"),
            "skel",
        ],
    );
    let skel = tmp.path().join("skel");

    // Client recorded the filter and commits/trees arrived.
    assert_eq!(
        git(
            &skel,
            &["config", "--get", "remote.origin.partialclonefilter"]
        )
        .trim(),
        "blob:none"
    );
    assert_eq!(git(&skel, &["rev-parse", "HEAD"]).trim(), tip);
    let (ok, _) = git_try(&skel, &["cat-file", "-e", &tree]);
    assert!(ok, "tree must be present after blob:none clone");
    let (ok, _) = git_try(&skel, &["cat-file", "-e", &tip]);
    assert!(ok, "commit must be present after blob:none clone");

    // Local object store has commits/trees only — blobs are promisor-missing.
    // (`cat-file -e` is true for promised oids, so we inspect real objects.)
    let local_objs = git(&skel, &["cat-file", "--batch-check", "--batch-all-objects"]);
    assert!(
        !local_objs.lines().any(|l| l.contains(" blob ")),
        "initial filter clone must not contain blob objects:\n{local_objs}"
    );
    assert!(
        local_object_missing(&skel, &readme_blob),
        "readme blob must be absent before follow-up fetch"
    );
    assert!(
        local_object_missing(&skel, &nested_blob),
        "nested blob must be absent before follow-up fetch"
    );

    // Follow-up: checkout triggers promisor lazy-fetch of needed blobs.
    git(&skel, &["checkout", "-q", "HEAD"]);
    git(&skel, &["fsck", "--strict"]);

    assert!(
        !local_object_missing(&skel, &readme_blob),
        "readme blob fetchable after checkout"
    );
    assert!(
        !local_object_missing(&skel, &nested_blob),
        "nested blob fetchable after checkout"
    );
    assert_eq!(
        std::fs::read_to_string(skel.join("readme.txt")).unwrap(),
        "hello partial v2\n"
    );
    assert_eq!(
        std::fs::read_to_string(skel.join("dir/nested.txt")).unwrap(),
        "nested content\n"
    );
}

/// `blob:limit` keeps small blobs in the initial pack and omits large ones
/// until a follow-up fetch.
#[test]
fn partial_clone_blob_limit_then_fetch_large() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("limit")]);

    write_file(&src, "small.txt", "ok\n");
    let large = "Y".repeat(8 * 1024);
    write_file(&src, "large.bin", &large);
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "mixed"]);
    git(&src, &["push", "-q", "origin", "main"]);

    let small_oid = git(&src, &["rev-parse", "HEAD:small.txt"])
        .trim()
        .to_string();
    let large_oid = git(&src, &["rev-parse", "HEAD:large.bin"])
        .trim()
        .to_string();

    git(
        tmp.path(),
        &[
            "clone",
            "-q",
            "--filter=blob:limit=1k",
            "--no-checkout",
            &server.url("limit"),
            "lim",
        ],
    );
    let lim = tmp.path().join("lim");

    assert!(
        !local_object_missing(&lim, &small_oid),
        "small blob under limit should be present initially"
    );
    assert!(
        local_object_missing(&lim, &large_oid),
        "large blob over limit must be absent initially"
    );

    // Explicit follow-up fetch of the missing blob oid.
    git(&lim, &["fetch", "-q", "origin", &large_oid]);
    assert!(
        !local_object_missing(&lim, &large_oid),
        "large blob fetchable in follow-up"
    );
    assert_eq!(
        git(&lim, &["cat-file", "-p", &large_oid]),
        large,
        "fetched large blob content"
    );
}

/// A push with a moderately large binary blob exercises multi-chunk
/// streaming ingest and multi-chunk fetch.
#[test]
fn large_blob_roundtrip() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("big")]);

    // ~8 MiB of pseudo-random (incompressible) bytes.
    let data = deterministic_noise(8 * 1024 * 1024, 0x9e3779b97f4a7c15);
    std::fs::write(src.join("blob.bin"), &data).unwrap();
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "big blob"]);
    git(&src, &["push", "-q", "origin", "main"]);

    git(tmp.path(), &["clone", "-q", &server.url("big"), "clone"]);
    let clone = tmp.path().join("clone");
    git(&clone, &["fsck", "--strict"]);
    let round_tripped = std::fs::read(clone.join("blob.bin")).unwrap();
    assert!(
        round_tripped == data,
        "cloned blob differs: {} vs {} bytes",
        round_tripped.len(),
        data.len()
    );

    // The file API serves the same bytes.
    let (status, body) = server.get("/api/big/file/main/blob.bin");
    assert_eq!(status, 200);
    assert!(
        body == data,
        "file API blob differs: {} vs {} bytes",
        body.len(),
        data.len()
    );
}

/// Compare our blame API against `git blame --line-porcelain` for `path` at
/// the source repo's HEAD.
fn assert_blame_matches(server: &TestServer, src: &std::path::Path, path: &str) {
    let repo_name = {
        // Derive repo name from the remote URL configured in `src`.
        let url = git(src, &["remote", "get-url", "origin"]);
        url.trim()
            .rsplit('/')
            .next()
            .unwrap()
            .trim_end_matches(".git")
            .to_string()
    };
    let porcelain = git(src, &["blame", "--line-porcelain", "HEAD", "--", path]);
    let expected: Vec<String> = porcelain
        .lines()
        .filter(|l| {
            // Header lines start with a 40-hex oid followed by line numbers.
            l.len() > 40
                && l.as_bytes()[..40].iter().all(|b| b.is_ascii_hexdigit())
                && l.as_bytes()[40] == b' '
        })
        .map(|l| l[..40].to_string())
        .collect();

    let (status, body) = server.get(&format!("/api/{repo_name}/blame/main/{path}"));
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&body));
    let blame: Value = serde_json::from_slice(&body).unwrap();
    let got: Vec<String> = blame["lines"]
        .as_array()
        .unwrap()
        .iter()
        .map(|l| l["commit"].as_str().unwrap().to_string())
        .collect();
    assert_eq!(
        got, expected,
        "blame mismatch for {path}: ours vs git blame"
    );
}

// ---------------------------------------------------------------------------
// Protocol edge cases driven without a git client (raw v2 POST bodies).
// ---------------------------------------------------------------------------

/// Build a protocol-v2 command request body (command, delim, args, flush).
fn v2_body(command: &str, args: &[&str]) -> Vec<u8> {
    use git_server::pktline;
    let mut b = Vec::new();
    b.extend_from_slice(&pktline::text_pkt(&format!("command={command}")));
    b.extend_from_slice(pktline::delim_pkt());
    for a in args {
        b.extend_from_slice(&pktline::text_pkt(a));
    }
    b.extend_from_slice(pktline::flush_pkt());
    b
}

/// Push one commit so the repo is non-empty; returns its tip oid.
fn seed_one_commit(server: &TestServer, tmp: &Path, repo: &str) -> String {
    let src = tmp.join(format!("seed-{repo}"));
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url(repo)]);
    write_file(&src, "f.txt", "seed\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "seed"]);
    git(&src, &["push", "-q", "origin", "main"]);
    git(&src, &["rev-parse", "HEAD"]).trim().to_string()
}

/// Every in-band fetch rejection answers 200 with an `ERR` pkt (not an HTTP
/// error), which is what lets stock git print the server's message.
#[test]
fn fetch_error_responses() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let tip = seed_one_commit(&server, tmp.path(), "errs");

    let post = |body: Vec<u8>| -> String {
        let (status, resp) = server.post_with_body(
            "/errs/git-upload-pack",
            &[("Content-Type", "application/x-git-upload-pack-request")],
            &body,
        );
        assert_eq!(status, 200);
        String::from_utf8_lossy(&resp).into_owned()
    };

    // No wants at all.
    let resp = post(v2_body("fetch", &["done"]));
    assert!(resp.contains("ERR fetch: no wants"), "{resp}");

    // Unsupported filter spec (partial clone supports blob/tree specs only).
    let resp = post(v2_body(
        "fetch",
        &[&format!("want {tip}"), "filter sparse:oid=abc", "done"],
    ));
    assert!(resp.contains("ERR unsupported filter-spec"), "{resp}");

    // Date-based shallow remains unsupported.
    let resp = post(v2_body(
        "fetch",
        &[&format!("want {tip}"), "deepen-since 1700000000", "done"],
    ));
    assert!(
        resp.contains("ERR unsupported fetch option: deepen-since"),
        "{resp}"
    );

    // Fetch from a repo that has never been pushed to.
    let (status, resp) = server.post_with_body(
        "/nosuchrepo/git-upload-pack",
        &[("Content-Type", "application/x-git-upload-pack-request")],
        &v2_body("fetch", &[&format!("want {tip}"), "done"]),
    );
    assert_eq!(status, 200);
    let resp = String::from_utf8_lossy(&resp);
    assert!(resp.contains("ERR repository is empty"), "{resp}");
}

/// git gzips large negotiation POST bodies (`Content-Encoding: gzip`); the
/// server must transparently decode them.
#[test]
fn gzip_encoded_request_body() {
    use std::io::Write;
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    seed_one_commit(&server, tmp.path(), "gz");

    let body = v2_body("ls-refs", &["peel", "symrefs"]);
    let mut enc =
        flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
    enc.write_all(&body).unwrap();
    let gzipped = enc.finish().unwrap();

    let (status, resp) = server.post_with_body(
        "/gz/git-upload-pack",
        &[
            ("Content-Type", "application/x-git-upload-pack-request"),
            ("Content-Encoding", "gzip"),
        ],
        &gzipped,
    );
    assert_eq!(status, 200);
    let text = String::from_utf8_lossy(&resp);
    assert!(text.contains("refs/heads/main"), "{text}");
    assert!(text.contains("HEAD"), "{text}");
}

/// A push whose pack bytes are garbage must be rejected without corrupting
/// anything: the ref is not created and the repo stays usable.
#[test]
fn corrupt_pack_push_rejected() {
    use git_server::pktline;
    let server = TestServer::start();

    let new_oid = "1".repeat(40);
    let zero = "0".repeat(40);
    let mut body = Vec::new();
    body.extend_from_slice(&pktline::text_pkt(&format!(
        "{zero} {new_oid} refs/heads/main\0report-status"
    )));
    body.extend_from_slice(pktline::flush_pkt());
    body.extend_from_slice(b"THIS IS NOT A PACKFILE");

    let (status, resp) = server.post_with_body(
        "/corrupt/git-receive-pack",
        &[("Content-Type", "application/x-git-receive-pack-request")],
        &body,
    );
    let text = String::from_utf8_lossy(&resp);
    assert!(status != 200 || text.contains("unpack"), "{status}: {text}");

    // The bad push left no trace: repo still reports EMPTY.
    let (status, body) = server.get("/api/corrupt");
    assert_eq!(status, 200);
    let s: Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(s["status"], "EMPTY", "{s}");
}

/// A push that promises ref updates but sends no pack is an error, not a
/// silent ref creation.
#[test]
fn push_without_pack_rejected() {
    use git_server::pktline;
    let server = TestServer::start();

    let new_oid = "2".repeat(40);
    let zero = "0".repeat(40);
    let mut body = Vec::new();
    body.extend_from_slice(&pktline::text_pkt(&format!(
        "{zero} {new_oid} refs/heads/main\0report-status"
    )));
    body.extend_from_slice(pktline::flush_pkt());

    let (status, resp) = server.post_with_body(
        "/nopack/git-receive-pack",
        &[("Content-Type", "application/x-git-receive-pack-request")],
        &body,
    );
    let text = String::from_utf8_lossy(&resp);
    assert!(
        status != 200 || text.contains("no pack"),
        "{status}: {text}"
    );
    let (_, body) = server.get("/api/nopack");
    let s: Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(s["status"], "EMPTY", "{s}");
}

/// Cloning a repo that has never been pushed to yields an empty local repo
/// (unborn-HEAD advertisement), which can then push normally.
#[test]
fn clone_empty_repo_then_push() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();

    git(
        tmp.path(),
        &["clone", "-q", &server.url("virgin"), "empty-clone"],
    );
    let clone = tmp.path().join("empty-clone");
    let (ok, _) = git_try(&clone, &["rev-parse", "--verify", "HEAD"]);
    assert!(!ok, "fresh clone of empty repo has no commits");

    // The clone is fully functional: commit and push upstream.
    write_file(&clone, "hello.txt", "first\n");
    git(&clone, &["add", "."]);
    git(&clone, &["commit", "-q", "-m", "first"]);
    git(&clone, &["push", "-q", "origin", "HEAD"]);

    let (_, body) = server.get("/api/virgin");
    let s: Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(s["status"], "READY", "{s}");
}

/// `git ls-remote` shows annotated tags with their peeled (`^{}`) targets,
/// which exercises the ls-refs `peel` argument.
#[test]
fn ls_remote_peels_annotated_tags() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("peel")]);
    write_file(&src, "f.txt", "content\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "c1"]);
    git(&src, &["tag", "-a", "v1", "-m", "annotated"]);
    git(&src, &["push", "-q", "origin", "main", "v1"]);
    let commit = git(&src, &["rev-parse", "HEAD"]).trim().to_string();
    let tag = git(&src, &["rev-parse", "v1"]).trim().to_string();
    assert_ne!(commit, tag, "annotated tag is its own object");

    let out = git(&src, &["ls-remote", "origin"]);
    assert!(
        out.contains(&format!("{tag}\trefs/tags/v1")),
        "tag object listed: {out}"
    );
    assert!(
        out.contains(&format!("{commit}\trefs/tags/v1^{{}}")),
        "peeled target listed: {out}"
    );
}

/// A path that flips between file and directory across commits exercises the
/// tree-diff merge walk's rename-kind arms (file->dir and dir->file).
#[test]
fn path_flips_between_file_and_directory() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();
    git(&src, &["init", "-q", "-b", "main", "."]);
    git(&src, &["remote", "add", "origin", &server.url("flip")]);

    // Commit 1: `x` is a file.
    write_file(&src, "x", "plain file\n");
    write_file(&src, "keep.txt", "constant\n");
    git(&src, &["add", "."]);
    git(&src, &["commit", "-q", "-m", "x as file"]);
    git(&src, &["push", "-q", "origin", "main"]);

    // Commit 2: `x` becomes a directory.
    std::fs::remove_file(src.join("x")).unwrap();
    write_file(&src, "x/inner.txt", "now nested\n");
    git(&src, &["add", "-A", "."]);
    git(&src, &["commit", "-q", "-m", "x as dir"]);
    git(&src, &["push", "-q", "origin", "main"]);

    // Commit 3: back to a file.
    git(&src, &["rm", "-q", "-r", "x"]);
    write_file(&src, "x", "file again\n");
    git(&src, &["add", "-A", "."]);
    git(&src, &["commit", "-q", "-m", "x as file again"]);
    git(&src, &["push", "-q", "origin", "main"]);

    // The server-side file APIs agree with the final shape…
    let (status, body) = server.get("/api/flip/file/main/x");
    assert_eq!(status, 200);
    assert_eq!(body, b"file again\n");
    let (status, _) = server.get("/api/flip/tree/main/x");
    assert_eq!(status, 404, "x is not a directory at HEAD");

    // …the middle commit is browsable…
    let mid = git(&src, &["rev-parse", "HEAD~1"]).trim().to_string();
    let (status, body) = server.get(&format!("/api/flip/file/{mid}/x/inner.txt"));
    assert_eq!(status, 200);
    assert_eq!(body, b"now nested\n");

    // …and a fresh clone of the full history is intact.
    git(tmp.path(), &["clone", "-q", &server.url("flip"), "flipclone"]);
    git(&tmp.path().join("flipclone"), &["fsck", "--strict"]);
}
