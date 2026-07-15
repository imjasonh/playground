//! Large-repo benchmark: git-fuse against a real project served over the
//! localhost harness. Defaults to a bare mirror of kubernetes/kubernetes
//! (~1.3 GiB, ~25k files at HEAD, 1200+ refs).
//!
//! ```bash
//! cargo bench --bench large_repo
//! # reuse an existing bare mirror instead of cloning:
//! LARGE_REPO_GIT_DIR=/path/to/kubernetes.git cargo bench --bench large_repo
//! # also measure the full (all refs + history) fetch:
//! LARGE_REPO_FULL=1 cargo bench --bench large_repo
//! ```
//!
//! Measured flow, mirroring how the mount is meant to be used:
//!
//! 1. **time to first byte, cold** — mount with an empty cache and read one
//!    file; the baseline is `git clone --depth=1 --single-branch` + read.
//!    The mount's background shallow fetch of the default branch races the
//!    read; the read itself is served by the JSON API in a few round trips.
//! 2. **shallow warm** — how long until the default branch is fully local.
//! 3. **`ls -R` of the whole tree** once shallow-warm, vs `ls -R` over the
//!    baseline clone's worktree.
//! 4. **history on demand** — read a file at `HEAD~1000`, which no staged
//!    fetch has brought in: served remotely at once, then fetched into the
//!    cache in the background. Baseline: targeted `git fetch <sha>` + read.

use git_fuse::testutil::{fuse_available, TempDir, TestServer};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

const DEFAULT_URL: &str = "https://github.com/kubernetes/kubernetes.git";

fn git_in(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("--git-dir")
        .arg(dir)
        .args(args)
        .output()
        .expect("git");
    assert!(
        out.status.success(),
        "git --git-dir {} {:?} failed: {}",
        dir.display(),
        args,
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn git(args: &[&str]) {
    let out = Command::new("git")
        .args(args)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .output()
        .expect("git");
    assert!(
        out.status.success(),
        "git {:?} failed: {}",
        args,
        String::from_utf8_lossy(&out.stderr)
    );
}

/// The upstream bare mirror: `LARGE_REPO_GIT_DIR` if set, else a cached
/// clone of `LARGE_REPO_URL` under `target/`.
fn upstream() -> PathBuf {
    if let Some(dir) = std::env::var_os("LARGE_REPO_GIT_DIR") {
        return PathBuf::from(dir);
    }
    let url = std::env::var("LARGE_REPO_URL").unwrap_or_else(|_| DEFAULT_URL.to_string());
    let dest = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/large-repo-upstream.git");
    if !dest.join("HEAD").exists() {
        eprintln!("cloning {url} into {} (one-time, large)…", dest.display());
        git(&["clone", "--bare", &url, dest.to_str().unwrap()]);
    }
    dest
}

/// Recursively walk a directory, counting entries (no content reads) —
/// what `ls -R` does.
fn walk_count(dir: &Path) -> usize {
    let mut n = 0;
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d).expect("read_dir") {
            let entry = entry.unwrap();
            if entry.file_name() == ".git" {
                continue; // baseline clone: compare working-tree entries only
            }
            n += 1;
            if entry.file_type().unwrap().is_dir() {
                stack.push(entry.path());
            }
        }
    }
    n
}

fn main() {
    if !fuse_available() {
        eprintln!("SKIP: FUSE is not available on this host");
        return;
    }
    let delay_ms: u64 = std::env::var("BENCH_DELAY_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(25);

    let upstream = upstream();
    // On-demand sha fetches need this (git-server always allows sha wants).
    git_in(
        &upstream,
        &["config", "uploadpack.allowAnySHA1InWant", "true"],
    );
    let head_branch = git_in(&upstream, &["symbolic-ref", "HEAD"])
        .trim()
        .to_string();
    let head = git_in(&upstream, &["rev-parse", "HEAD"]).trim().to_string();
    let old = git_in(&upstream, &["rev-parse", "HEAD~1000"])
        .trim()
        .to_string();
    // A deterministic mid-depth file that exists at both commits.
    let probe_file = git_in(&upstream, &["ls-tree", "-r", "--name-only", &old])
        .lines()
        .find(|p| p.matches('/').count() == 2 && p.ends_with(".go"))
        .expect("no probe file")
        .to_string();
    let objects = git_in(&upstream, &["count-objects", "-v"]);
    eprintln!(
        "upstream: {} ({}), HEAD {head}, probe {probe_file}",
        upstream.display(),
        objects
            .lines()
            .find(|l| l.starts_with("in-pack"))
            .unwrap_or("?")
    );

    let server = TestServer::start(&upstream);
    server.set_delay(Duration::from_millis(delay_ms));

    // --- Baseline: shallow single-branch clone + reads. -------------------
    let clone_dir = TempDir::new("large-clone");
    let work = clone_dir.path().join("work");
    let t = Instant::now();
    git(&[
        "clone",
        "--quiet",
        "--depth=1",
        "--single-branch",
        &server.url(),
        work.to_str().unwrap(),
    ]);
    let clone_done = t.elapsed();
    std::fs::read(work.join(&probe_file)).expect("baseline read");
    let clone_first_byte = t.elapsed();
    let t = Instant::now();
    let clone_entries = walk_count(&work);
    let clone_ls = t.elapsed();
    // Baseline "history on demand": targeted fetch of the old sha, then read.
    let t = Instant::now();
    git(&[
        "-C",
        work.to_str().unwrap(),
        "fetch",
        "--quiet",
        "--depth=1",
        "origin",
        &old,
    ]);
    let out = Command::new("git")
        .args(["-C", work.to_str().unwrap(), "cat-file", "blob"])
        .arg(format!("{old}:{probe_file}"))
        .output()
        .expect("git cat-file");
    assert!(out.status.success());
    let clone_old_read = t.elapsed();

    // --- git-fuse: cold mount, then staged warmup. -------------------------
    let mnt = TempDir::new("large-mnt");
    let cache = TempDir::new("large-cache");
    let mut opts = git_fuse::Options::new(server.url());
    opts.cache_dir = Some(cache.path().join("repo.git"));
    opts.verbose = std::env::var_os("GIT_FUSE_VERBOSE").is_some();
    let t = Instant::now();
    let mount = git_fuse::mount(mnt.path(), opts).expect("mount");
    let commit_dir = mnt.path().join(format!("commits/{head}"));
    std::fs::read(commit_dir.join(&probe_file)).expect("fuse read");
    let fuse_first_byte = t.elapsed();

    // Composition check while cold: refs file matches upstream HEAD.
    let ref_path = mnt.path().join(format!(
        "refs/{}",
        head_branch.strip_prefix("refs/").unwrap()
    ));
    assert_eq!(
        std::fs::read_to_string(&ref_path).unwrap().trim(),
        head,
        "refs file must expose the head sha"
    );

    let t = Instant::now();
    assert!(
        mount.wait_local_usable(Duration::from_secs(600)),
        "shallow warmup"
    );
    let shallow_warm = t.elapsed();

    let t = Instant::now();
    let fuse_entries = walk_count(&commit_dir);
    let fuse_ls = t.elapsed();
    assert_eq!(fuse_entries, clone_entries, "traversals must agree");

    // History on demand: HEAD~1000 isn't local (shallow default branch
    // only); the read is served by the remote API immediately.
    let t = Instant::now();
    let data =
        std::fs::read(mnt.path().join(format!("commits/{old}/{probe_file}"))).expect("old read");
    let fuse_old_read = t.elapsed();
    assert!(!data.is_empty());

    let full = if std::env::var_os("LARGE_REPO_FULL").is_some() {
        let t = Instant::now();
        assert!(
            mount.wait_warm(Duration::from_secs(3600)),
            "full fetch (all refs + history)"
        );
        Some(t.elapsed())
    } else {
        None
    };

    println!("\nlarge_repo: {clone_entries} entries at HEAD, server latency {delay_ms} ms");
    println!(
        "  {:<44} {:>12} {:>16}",
        "scenario", "git-fuse", "shallow clone"
    );
    let row = |name: &str, fuse: Duration, base: Duration| {
        println!(
            "  {:<44} {:>12} {:>16}",
            name,
            format!("{fuse:.2?}"),
            format!("{base:.2?}")
        );
    };
    row(
        "time to first byte, cold",
        fuse_first_byte,
        clone_first_byte,
    );
    row(
        "ls -R whole tree (fuse: shallow-warm cache)",
        fuse_ls,
        clone_ls,
    );
    row(
        "read a file at HEAD~1000 (history on demand)",
        fuse_old_read,
        clone_old_read,
    );
    println!(
        "  {:<44} {:>12} {:>16}",
        "default branch fully local after",
        format!("{shallow_warm:.2?}"),
        format!("{clone_done:.2?} (clone)")
    );
    if let Some(full) = full {
        println!(
            "  {:<44} {:>12}",
            "all refs + full history local after",
            format!("{full:.2?}")
        );
    }
}
