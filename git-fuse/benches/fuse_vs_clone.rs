//! Measures git-fuse against the thing it replaces: shallow-cloning a repo
//! to read files out of it. Run with `cargo bench --bench fuse_vs_clone`.
//!
//! Scenarios (server latency injectable via BENCH_DELAY_MS, default 25 —
//! roughly a same-continent HTTP round trip; 0 measures pure overhead):
//!
//! * **time to first byte, cold**: nothing local at all →
//!   read one file. git-fuse answers with one refs lookup + one tree walk +
//!   one blob GET; the baseline must finish a `git clone --depth=1` first.
//! * **cold full read**: walk and read every file in the tree, starting
//!   cold. The baseline amortizes its clone across all files; git-fuse pays
//!   one HTTP GET per directory + per file until the background fetch
//!   lands, then serves locally.
//! * **warm full read**: the same walk once the cache is populated —
//!   git-fuse must not be meaningfully slower than reading a local clone.

use git_fuse::testutil::{fuse_available, Spec, TempDir, TestRepo, TestServer};
use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

/// Repo shape: `DIRS` directories of `FILES_PER_DIR` source-sized files,
/// plus one incompressible `BLOB_BYTES` asset — the thing that makes real
/// clones slow while a single-file read stays cheap.
const DIRS: usize = 20;
const FILES_PER_DIR: usize = 10;
const FILE_BYTES: usize = 4 << 10;
const BLOB_BYTES: usize = 24 << 20;

/// xorshift64* — fast incompressible bytes so git's deltification and zlib
/// can't shrink the bench blob into meaninglessness.
fn random_bytes(mut seed: u64, len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    while out.len() < len {
        seed ^= seed >> 12;
        seed ^= seed << 25;
        seed ^= seed >> 27;
        out.extend_from_slice(&seed.wrapping_mul(0x2545_F491_4F6C_DD1D).to_le_bytes());
    }
    out.truncate(len);
    out
}

fn build_repo() -> (TestRepo, String) {
    let repo = TestRepo::new();
    let mut contents: Vec<(String, Vec<u8>)> = Vec::new();
    for d in 0..DIRS {
        for f in 0..FILES_PER_DIR {
            let path = format!("dir-{d:02}/file-{f:02}.txt");
            let body: Vec<u8> = format!("{path}\n")
                .into_bytes()
                .into_iter()
                .cycle()
                .take(FILE_BYTES)
                .collect();
            contents.push((path, body));
        }
    }
    contents.push(("assets/blob.bin".to_string(), random_bytes(42, BLOB_BYTES)));
    // A little history so the full fetch has something the shallow one
    // doesn't.
    repo.commit("base", &[Spec::File("README.md", b"bench repo\n")]);
    let specs: Vec<Spec> = contents.iter().map(|(p, c)| Spec::File(p, c)).collect();
    let sha = repo.commit("tree", &specs);
    (repo, sha)
}

/// Recursively read every regular file under `dir`; returns (files, bytes).
fn read_all(dir: &Path) -> (usize, u64) {
    let mut files = 0;
    let mut bytes = 0u64;
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d).expect("read_dir") {
            let entry = entry.unwrap();
            let ft = entry.file_type().unwrap();
            if ft.is_dir() {
                if entry.file_name() == ".git" {
                    continue; // baseline clone: compare working-tree files only
                }
                stack.push(entry.path());
            } else if ft.is_file() {
                files += 1;
                bytes += std::fs::read(entry.path()).expect("read").len() as u64;
            }
        }
    }
    (files, bytes)
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

struct Row {
    name: &'static str,
    fuse: Duration,
    clone: Duration,
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

    let (repo, sha) = build_repo();
    let server = TestServer::start(&repo);
    server.set_delay(Duration::from_millis(delay_ms));
    let probe_file = "dir-00/file-00.txt";
    let mut rows = Vec::new();

    // --- Baseline: shallow clone, then read. -----------------------------
    let clone_dir = TempDir::new("bench-clone");
    let work = clone_dir.path().join("work");
    let t = Instant::now();
    git(&[
        "clone",
        "--quiet",
        "--depth=1",
        &server.url(),
        work.to_str().unwrap(),
    ]);
    let clone_done = t.elapsed();
    std::fs::read(work.join(probe_file)).expect("baseline read");
    let clone_first_byte = t.elapsed();
    let (n, _) = read_all(&work.join("."));
    let clone_full = t.elapsed();
    assert_eq!(n, DIRS * FILES_PER_DIR + 2);
    let t = Instant::now();
    let (_, _) = read_all(&work.join("."));
    let clone_warm = t.elapsed();

    // --- git-fuse: cold mount. -------------------------------------------
    let mnt = TempDir::new("bench-mnt");
    let cache = TempDir::new("bench-cache");
    let mut opts = git_fuse::Options::new(server.url());
    opts.cache_dir = Some(cache.path().join("repo.git"));
    let t = Instant::now();
    let mount = git_fuse::mount(mnt.path(), opts).expect("mount");
    let commit_dir = mnt.path().join(format!("commits/{sha}"));
    std::fs::read(commit_dir.join(probe_file)).expect("fuse read");
    let fuse_first_byte = t.elapsed();
    let (n, _) = read_all(&commit_dir);
    let fuse_full_cold = t.elapsed();
    assert_eq!(n, DIRS * FILES_PER_DIR + 2);

    rows.push(Row {
        name: "time to first byte (cold)",
        fuse: fuse_first_byte,
        clone: clone_first_byte,
    });
    rows.push(Row {
        name: "read whole tree (cold)",
        fuse: fuse_full_cold,
        clone: clone_full,
    });

    // --- git-fuse: warm (cache fetched, kernel cache dropped by remount). -
    assert!(mount.wait_warm(Duration::from_secs(120)), "warmup");
    drop(mount);
    let mut opts = git_fuse::Options::new(server.url());
    opts.cache_dir = Some(cache.path().join("repo.git"));
    let mount = git_fuse::mount(mnt.path(), opts).expect("remount");
    let t = Instant::now();
    let (_, _) = read_all(&commit_dir);
    let fuse_full_warm = t.elapsed();
    rows.push(Row {
        name: "read whole tree (warm cache)",
        fuse: fuse_full_warm,
        clone: clone_warm,
    });

    // Second pass: kernel page cache is hot on both sides.
    let t = Instant::now();
    let (_, _) = read_all(&commit_dir);
    let fuse_full_hot = t.elapsed();
    rows.push(Row {
        name: "read whole tree (hot again)",
        fuse: fuse_full_hot,
        clone: clone_warm,
    });
    drop(mount);

    let files = DIRS * FILES_PER_DIR + 1;
    println!(
        "\nfuse_vs_clone: {files} files x {FILE_BYTES} B + one {} MiB asset, \
         server latency {delay_ms} ms (BENCH_DELAY_MS to change)",
        BLOB_BYTES >> 20
    );
    println!("  baseline clone --depth=1 alone: {clone_done:?}\n");
    println!(
        "  {:<32} {:>12} {:>16}",
        "scenario", "git-fuse", "shallow clone"
    );
    for r in &rows {
        println!(
            "  {:<32} {:>12} {:>16}   ({})",
            r.name,
            format!("{:?}", r.fuse),
            format!("{:?}", r.clone),
            speedup(r.fuse, r.clone),
        );
    }
}

fn speedup(fuse: Duration, clone: Duration) -> String {
    let f = fuse.as_secs_f64();
    let c = clone.as_secs_f64();
    if f <= c {
        format!("{:.1}x faster", c / f)
    } else {
        format!("{:.1}x slower", f / c)
    }
}
