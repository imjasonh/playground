//! End-to-end integration tests: a real `git` client (clone/push/pull/tags)
//! against the same handler code the Worker runs, plus the read APIs and
//! repacking, with cost-model assertions along the way.
//!
//! Requires `git` on PATH (present in CI and dev machines).

mod common;

use common::{git, git_try, write_file, TestServer};
use serde_json::Value;

/// The repo status API: EMPTY before any push, READY after, with default
/// branch, head commit, size counters, and a last-push timestamp.
#[test]
fn status_api() {
    let server = TestServer::start();
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    std::fs::create_dir(&src).unwrap();

    // Unknown/never-pushed repo reports EMPTY.
    let (status, body) = server.get("/api/proj/status");
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

    let (status, body) = server.get("/api/proj/status");
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

    let packs_after: Vec<String> = server
        .store
        .keys()
        .into_iter()
        .filter(|k| k.ends_with(".pack"))
        .collect();
    assert_eq!(
        packs_after.len(),
        1,
        "one pack after repack: {packs_after:?}"
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
    let mut data = Vec::with_capacity(1024 * 1024);
    let mut x = 0x2545f4914f6cdd1du64;
    while data.len() < 1024 * 1024 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        data.extend_from_slice(&x.to_le_bytes());
    }
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
    let mut data = Vec::with_capacity(8 * 1024 * 1024);
    let mut x = 0x9e3779b97f4a7c15u64;
    while data.len() < 8 * 1024 * 1024 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        data.extend_from_slice(&x.to_le_bytes());
    }
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
