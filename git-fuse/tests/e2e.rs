//! End-to-end tests: a real FUSE mount against a real localhost server
//! (smart-HTTP via `git http-backend` + git-server's JSON read API shape),
//! exercised through ordinary filesystem syscalls — including a literal
//! `ls -R <mount>/commits/$(cat <mount>/refs/heads/main)`.
//!
//! Every test skips (with a note) when the host can't mount FUSE
//! (`/dev/fuse` missing or no fusermount binary).

use git_fuse::testutil::{
    fuse_available, Spec, TempDir, TestRepo, TestServer, CAT_API_FILE, CAT_SMART,
};
use git_fuse::{mount, Mount, Options};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

macro_rules! require_fuse {
    () => {
        if !fuse_available() {
            eprintln!("SKIP: FUSE is not available on this host");
            return;
        }
    };
}

/// A mounted test fixture. Field order = drop order: the mount must be torn
/// down before the mountpoint TempDir tries to remove itself.
struct Fixture {
    mount: Option<Mount>,
    repo: TestRepo,
    server: TestServer,
    mnt: TempDir,
    cache: TempDir,
}

/// Short TTL so tests that push after mount see the new refs quickly.
const TEST_REFS_TTL: Duration = Duration::from_millis(100);

const WAIT: Duration = Duration::from_secs(60);

impl Fixture {
    fn options(server: &TestServer, cache: &Path) -> Options {
        let mut opts = Options::new(server.url());
        opts.cache_dir = Some(cache.to_path_buf());
        opts.refs_ttl = TEST_REFS_TTL;
        opts
    }

    /// Repo with a couple of commits, mounted with warmup on.
    fn new() -> Fixture {
        let repo = TestRepo::new();
        repo.commit(
            "first",
            &[
                Spec::File("README.md", b"hello git-fuse\n"),
                Spec::File("src/lib.rs", b"pub fn one() -> u32 { 1 }\n"),
                Spec::File("src/deep/nested/mod.rs", b"// nested\n"),
            ],
        );
        repo.commit(
            "second",
            &[Spec::File("src/lib.rs", b"pub fn one() -> u32 { 2 }\n")],
        );
        Self::with_repo(repo)
    }

    fn with_repo(repo: TestRepo) -> Fixture {
        let server = TestServer::start(repo.bare());
        Self::with_server(repo, server, true)
    }

    fn with_server(repo: TestRepo, server: TestServer, warmup: bool) -> Fixture {
        let mnt = TempDir::new("mnt");
        let cache = TempDir::new("cache");
        let mut opts = Self::options(&server, &cache.path().join("repo.git"));
        opts.warmup = warmup;
        opts.verbose = true;
        let mount = mount(mnt.path(), opts).expect("mount");
        Fixture {
            mount: Some(mount),
            repo,
            server,
            mnt,
            cache,
        }
    }

    fn path(&self, rel: &str) -> PathBuf {
        self.mnt.path().join(rel)
    }

    fn commit_dir(&self, sha: &str) -> PathBuf {
        self.path(&format!("commits/{sha}"))
    }

    /// The shared bare-repo cache directory backing the mount.
    fn cache_git_dir(&self) -> PathBuf {
        self.cache.path().join("repo.git")
    }

    fn cat(&self, rel: &str) -> Vec<u8> {
        std::fs::read(self.path(rel)).unwrap_or_else(|e| panic!("read {rel}: {e}"))
    }

    fn cat_ref(&self, rel: &str) -> String {
        String::from_utf8(self.cat(rel)).unwrap().trim().to_string()
    }

    fn remount(&mut self, warmup: bool) {
        self.mount.take(); // unmount first
        let mut opts = Self::options(&self.server, &self.cache.path().join("repo.git"));
        opts.warmup = warmup;
        opts.verbose = true;
        self.mount = Some(mount(self.mnt.path(), opts).expect("remount"));
    }

    fn mount_ref(&self) -> &Mount {
        self.mount.as_ref().unwrap()
    }
}

/// Does the (cache) repo at `git_dir` have this object locally?
fn git_has_object(git_dir: &Path, sha: &str) -> bool {
    std::process::Command::new("git")
        .arg("--git-dir")
        .arg(git_dir)
        .args(["cat-file", "-e", sha])
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Poll `cond` until true or the deadline passes.
fn eventually(what: &str, timeout: Duration, mut cond: impl FnMut() -> bool) {
    let deadline = Instant::now() + timeout;
    while Instant::now() < deadline {
        if cond() {
            return;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    panic!("timed out waiting for {what}");
}

/// Recursively collect regular-file and symlink paths under `dir`, relative
/// to it — what the mount presents, to compare against `git ls-tree -r`.
fn walk(dir: &Path) -> Vec<String> {
    fn inner(root: &Path, dir: &Path, out: &mut Vec<String>) {
        for entry in std::fs::read_dir(dir).expect("read_dir") {
            let entry = entry.unwrap();
            let ft = entry.file_type().unwrap();
            let path = entry.path();
            if ft.is_dir() {
                inner(root, &path, out);
            } else {
                out.push(
                    path.strip_prefix(root)
                        .unwrap()
                        .to_string_lossy()
                        .into_owned(),
                );
            }
        }
    }
    let mut out = Vec::new();
    inner(dir, dir, &mut out);
    out.sort();
    out
}

#[test]
fn refs_expose_shas_and_listing() {
    require_fuse!();
    let f = Fixture::new();
    f.repo.tag("v1");
    f.repo.branch("feature");

    let main_sha = f.repo.rev_parse("refs/heads/main");
    eventually("refs to appear", WAIT, || {
        f.path("refs/heads/feature").exists()
    });

    assert_eq!(f.cat_ref("refs/heads/main"), main_sha);
    assert_eq!(f.cat_ref("refs/HEAD"), main_sha);
    assert_eq!(f.cat_ref("refs/tags/v1"), f.repo.rev_parse("refs/tags/v1"));
    assert_eq!(f.cat_ref("refs/heads/feature"), main_sha);

    // Ref files read as exactly "<sha>\n" and stat that size.
    let raw = f.cat("refs/heads/main");
    assert_eq!(raw.len(), 41);
    assert_eq!(raw[40], b'\n');
    let meta = std::fs::metadata(f.path("refs/heads/main")).unwrap();
    assert_eq!(meta.len(), 41);

    // Listings mirror the ref namespace.
    let names = |rel: &str| -> Vec<String> {
        let mut v: Vec<String> = std::fs::read_dir(f.path(rel))
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        v.sort();
        v
    };
    assert_eq!(names(""), ["commits", "refs"]);
    assert_eq!(names("refs"), ["HEAD", "heads", "tags"]);
    assert_eq!(names("refs/heads"), ["feature", "main"]);
    assert_eq!(names("refs/tags"), ["v1"]);
}

#[test]
fn read_files_at_any_commit() {
    require_fuse!();
    let repo = TestRepo::new();
    let first = repo.commit("first", &[Spec::File("f.txt", b"version 1\n")]);
    let second = repo.commit("second", &[Spec::File("f.txt", b"version 2\n")]);
    let f = Fixture::with_repo(repo);

    // Tip content.
    assert_eq!(f.cat(&format!("commits/{second}/f.txt")), b"version 2\n");
    // History (only reachable via remote API until the full fetch lands —
    // works either way).
    assert_eq!(f.cat(&format!("commits/{first}/f.txt")), b"version 1\n");
}

#[test]
fn ls_recursive_composition_matches_git() {
    require_fuse!();
    let repo = TestRepo::new();
    let mut specs: Vec<(String, Vec<u8>)> = Vec::new();
    // A wide directory (multiple readdir batches) plus nesting.
    for i in 0..300 {
        specs.push((
            format!("wide/file-{i:03}.txt"),
            format!("contents {i}\n").into_bytes(),
        ));
    }
    specs.push(("a/b/c/d/deep.txt".to_string(), b"deep\n".to_vec()));
    specs.push(("top.txt".to_string(), b"top\n".to_vec()));
    let spec_refs: Vec<Spec> = specs.iter().map(|(p, c)| Spec::File(p, c)).collect();
    let sha = repo.commit("tree", &spec_refs);
    let f = Fixture::with_repo(repo);

    // The exact composition from the requirements:
    //   ls -R <mount>/commits/$(cat <mount>/refs/heads/main)
    let out = std::process::Command::new("sh")
        .arg("-c")
        .arg(r#"ls -R "$1/commits/$(cat "$1/refs/heads/main")""#)
        .arg("sh")
        .arg(f.mnt.path())
        .output()
        .expect("run ls -R");
    assert!(
        out.status.success(),
        "ls -R failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let listing = String::from_utf8_lossy(&out.stdout);
    assert!(listing.contains("deep.txt"));
    assert!(listing.contains("file-299.txt"));
    assert!(listing.contains("top.txt"));

    // Full traversal matches `git ls-tree -r` exactly.
    let want = f.repo.ls_tree_recursive(&sha);
    let got = walk(&f.commit_dir(&sha));
    assert_eq!(got, want);

    // And the contents round-trip.
    assert_eq!(
        f.cat(&format!("commits/{sha}/wide/file-123.txt")),
        b"contents 123\n"
    );
    assert_eq!(f.cat(&format!("commits/{sha}/a/b/c/d/deep.txt")), b"deep\n");
}

#[test]
fn cold_reads_never_wait_for_a_clone() {
    require_fuse!();
    let repo = TestRepo::new();
    let sha = repo.commit("only", &[Spec::File("fast.txt", b"first byte fast\n")]);
    let server = TestServer::start(repo.bare());
    // Smart-HTTP is broken: no clone or fetch can ever succeed, so every
    // successful read below was served by the JSON API alone.
    server.set_fail_smart(true);
    let f = Fixture::with_server(repo, server, true);

    assert_eq!(f.cat_ref("refs/heads/main"), sha);
    assert_eq!(
        f.cat(&format!("commits/{sha}/fast.txt")),
        b"first byte fast\n"
    );
    let listed = walk(&f.commit_dir(&sha));
    assert_eq!(listed, ["fast.txt"]);
    assert!(
        f.server.count(CAT_API_FILE) > 0,
        "reads must have used the API"
    );
    assert!(!f.mount_ref().wait_local_usable(Duration::ZERO));
}

#[test]
fn warmup_goes_shallow_then_full_and_serves_offline() {
    require_fuse!();
    let repo = TestRepo::new();
    let old = repo.commit("old", &[Spec::File("f.txt", b"old\n")]);
    let new = repo.commit("new", &[Spec::File("f.txt", b"new\n")]);
    let f = Fixture::with_repo(repo);

    assert!(f.mount_ref().wait_local_usable(WAIT), "shallow fetch");
    assert!(f.mount_ref().wait_warm(WAIT), "full fetch");
    assert!(f.server.count(CAT_SMART) > 0, "warmup used smart-HTTP");

    // With the whole remote down (both surfaces), everything still reads
    // from the local cache — including pre-shallow history.
    f.server.set_fail_api(true);
    f.server.set_fail_smart(true);
    std::thread::sleep(TEST_REFS_TTL * 2); // let the refs snapshot expire
    assert_eq!(f.cat_ref("refs/heads/main"), new);
    assert_eq!(f.cat(&format!("commits/{new}/f.txt")), b"new\n");
    assert_eq!(f.cat(&format!("commits/{old}/f.txt")), b"old\n");
}

#[test]
fn shared_cache_is_reused_by_the_next_mount() {
    require_fuse!();
    let repo = TestRepo::new();
    let sha = repo.commit("only", &[Spec::File("f.txt", b"cached\n")]);
    let mut f = Fixture::with_repo(repo);
    assert!(f.mount_ref().wait_warm(WAIT));

    // Remount over the same cache dir with the remote fully broken: the
    // second mount must be warm instantly and serve everything locally.
    f.server.set_fail_api(true);
    f.server.set_fail_smart(true);
    f.remount(true);
    assert!(
        f.mount_ref().wait_warm(Duration::ZERO),
        "pre-existing full cache should be warm immediately"
    );
    assert_eq!(f.cat_ref("refs/heads/main"), sha);
    assert_eq!(f.cat(&format!("commits/{sha}/f.txt")), b"cached\n");
}

#[test]
fn new_commits_are_discovered_after_mount() {
    require_fuse!();
    let f = Fixture::new();
    assert!(f.mount_ref().wait_warm(WAIT));
    let before = f.cat_ref("refs/heads/main");

    let after = f.repo.commit(
        "pushed after mount",
        &[Spec::File("later.txt", b"post-mount\n")],
    );
    assert_ne!(before, after);

    // The short refs TTL picks up the new head…
    eventually("new head to appear", WAIT, || {
        f.cat_ref("refs/heads/main") == after
    });
    // …and its content is readable immediately (remote API at worst).
    assert_eq!(
        f.cat(&format!("commits/{after}/later.txt")),
        b"post-mount\n"
    );

    // The ref change also triggers an incremental fetch that lands the new
    // commit's objects in the shared cache.
    eventually("incremental fetch to land", WAIT, || {
        git_has_object(&f.cache_git_dir(), &after)
    });
}

#[test]
fn symlinks_modes_and_binary_files() {
    require_fuse!();
    let repo = TestRepo::new();
    let binary: Vec<u8> = (0..=255u8).cycle().take(1 << 20).collect();
    let sha = repo.commit(
        "kinds",
        &[
            Spec::File("plain.txt", b"plain\n"),
            Spec::Exec("run.sh", b"#!/bin/sh\necho hi\n"),
            Spec::Symlink("link", "plain.txt"),
            Spec::File("blob.bin", &binary),
        ],
    );
    let f = Fixture::with_repo(repo);
    let base = f.commit_dir(&sha);

    // Regular file: read-only.
    use std::os::unix::fs::PermissionsExt;
    let plain = std::fs::metadata(base.join("plain.txt")).unwrap();
    assert_eq!(plain.permissions().mode() & 0o777, 0o444);
    assert_eq!(plain.len(), 6);

    // Executable bit survives.
    let exec = std::fs::metadata(base.join("run.sh")).unwrap();
    assert_ne!(exec.permissions().mode() & 0o111, 0);

    // Symlink resolves within the mount.
    let target = std::fs::read_link(base.join("link")).unwrap();
    assert_eq!(target, PathBuf::from("plain.txt"));
    assert_eq!(std::fs::read(base.join("link")).unwrap(), b"plain\n");

    // A larger binary blob round-trips exactly (multiple FUSE read calls).
    assert_eq!(std::fs::read(base.join("blob.bin")).unwrap(), binary);

    // Writes are refused: it's a read-only filesystem.
    assert!(std::fs::write(base.join("plain.txt"), b"nope").is_err());
    assert!(std::fs::create_dir(base.join("newdir")).is_err());
}

#[test]
fn missing_things_are_enoent() {
    require_fuse!();
    let repo = TestRepo::new();
    let sha = repo.commit("only", &[Spec::File("real.txt", b"x\n")]);
    let f = Fixture::with_repo(repo);

    let missing = [
        "refs/heads/nope".to_string(),
        "refs/nothere".to_string(),
        // A well-formed sha that doesn't exist.
        format!("commits/{}", "0".repeat(40)),
        // Malformed commit names.
        "commits/nothexnothexnothexnothexnothexnothexz".to_string(),
        "commits/abc123".to_string(),
        format!("commits/{sha}/absent.txt"),
    ];
    for rel in missing {
        let err = std::fs::metadata(f.path(&rel)).expect_err(&format!("{rel} should not exist"));
        assert_eq!(err.kind(), std::io::ErrorKind::NotFound, "{rel}: {err:?}");
    }

    // Descending *through* a file is ENOTDIR, not ENOENT.
    let err = std::fs::metadata(f.path(&format!("commits/{sha}/real.txt/not-a-dir")))
        .expect_err("path through a file should fail");
    assert_eq!(err.kind(), std::io::ErrorKind::NotADirectory);

    // Directories aren't readable as files; files aren't listable as dirs.
    assert!(std::fs::read(f.commit_dir(&sha)).is_err());
    assert!(std::fs::read_dir(f.path(&format!("commits/{sha}/real.txt"))).is_err());
}

#[test]
fn on_demand_fetch_expands_the_cache_beyond_the_staged_fetches() {
    require_fuse!();
    let repo = TestRepo::new();
    repo.commit("base", &[Spec::File("f.txt", b"base\n")]);
    // A commit the staged fetches can never bring in: it's unreachable from
    // every ref upstream (think force-pushed-away PR head).
    let dangling = repo.commit_dangling("dangling", &[Spec::File("orphan.txt", b"orphan\n")]);
    let f = Fixture::with_repo(repo);
    assert!(f.mount_ref().wait_warm(WAIT));

    // The staged fetches (now finished) can't have brought it in…
    assert!(!git_has_object(&f.cache_git_dir(), &dangling));
    // …but it's readable immediately via the remote API…
    assert_eq!(
        f.cat(&format!("commits/{dangling}/orphan.txt")),
        b"orphan\n"
    );
    // …and that read triggers a targeted `git fetch <sha>` into the cache.
    eventually("on-demand fetch to land", WAIT, || {
        git_has_object(&f.cache_git_dir(), &dangling)
    });

    // A fresh mount over the same cache serves it with the remote down.
    let mut f = f;
    f.server.set_fail_api(true);
    f.server.set_fail_smart(true);
    f.remount(true);
    assert_eq!(
        f.cat(&format!("commits/{dangling}/orphan.txt")),
        b"orphan\n"
    );
}

#[test]
fn submodule_pointers_are_hidden() {
    require_fuse!();
    let repo = TestRepo::new();
    let base = repo.commit("base", &[Spec::File("real.txt", b"x\n")]);
    let sha = repo.commit_gitlink("vendored", &base, "add gitlink");
    let f = Fixture::with_repo(repo);

    let listed = walk(&f.commit_dir(&sha));
    assert_eq!(listed, ["real.txt"], "gitlink must not be listed");
    assert!(!f.path(&format!("commits/{sha}/vendored")).exists());
}

#[test]
fn no_warmup_mode_serves_via_api_only() {
    require_fuse!();
    let repo = TestRepo::new();
    let sha = repo.commit("only", &[Spec::File("f.txt", b"api-only\n")]);
    let server = TestServer::start(repo.bare());
    let f = Fixture::with_server(repo, server, false);

    assert_eq!(f.cat_ref("refs/heads/main"), sha);
    assert_eq!(f.cat(&format!("commits/{sha}/f.txt")), b"api-only\n");
    assert_eq!(
        f.server.count(CAT_SMART),
        0,
        "no warmup means no smart-HTTP traffic"
    );
}
