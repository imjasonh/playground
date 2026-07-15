//! The shared local cache: a bare git repository, one per remote URL.
//!
//! The cache directory is created on first mount and reused (and updated) by
//! every later mount of the same remote. Object reads go through one
//! long-lived `git cat-file --batch-command` child process — git re-scans the
//! object store when a lookup misses, so objects landed by a concurrent fetch
//! become visible without respawning.
//!
//! Warming is staged so a cold mount never blocks on a full clone:
//!
//! 1. **shallow** — `git fetch --depth=1` of the **default branch only**
//!    (the tip tree + blobs of the branch almost every read wants first);
//! 2. **full** — `git fetch --unshallow` of **all refs and history** — or,
//!    in lazy-history mode, a `--depth=1` fetch of every ref tip (no
//!    optimistic history download).
//!
//! Both run on a background thread; [`WarmState`] tracks progress so callers
//! (and tests) can wait for a stage. Anything the staged fetches haven't
//! covered yet — another branch, old history, a dangling commit — is served
//! from the remote API and *also* fetched on demand
//! ([`LocalCache::fetch_commit_async`]) so the next read of it is local; in
//! lazy-history mode that on-demand fetch additionally deepens the shallow
//! clone until the requested commit connects to the ref tips, backfilling
//! the intervening history. When the ref refresh notices new remote heads,
//! [`LocalCache::fetch_async`] runs one incremental fetch at a time (which
//! accretes new commits without unshallowing, so tips moving forward keep
//! extending the cache in either mode).

use crate::vlog;
use std::collections::HashSet;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

/// Warmup stages, in order.
pub(crate) const STATE_COLD: u8 = 0;
pub(crate) const STATE_SHALLOW: u8 = 1;
pub(crate) const STATE_WARM: u8 = 2;

/// Warmup retry backoff: first retry quickly (a transient failure at mount
/// time shouldn't leave the cache shallow for long), then double up to the
/// cap so a long remote outage isn't hammered.
const WARMUP_RETRY_INITIAL: Duration = Duration::from_secs(1);
const WARMUP_RETRY_MAX: Duration = Duration::from_secs(300);
/// How often the backoff sleep checks for unmount.
const WARMUP_SHUTDOWN_POLL: Duration = Duration::from_millis(100);

/// Monotonic warmup progress, waitable with a timeout.
pub struct WarmState {
    level: Mutex<u8>,
    cond: Condvar,
}

impl WarmState {
    fn new() -> Arc<WarmState> {
        Arc::new(WarmState {
            level: Mutex::new(STATE_COLD),
            cond: Condvar::new(),
        })
    }

    fn advance(&self, to: u8) {
        let mut level = self.level.lock().unwrap();
        if *level < to {
            *level = to;
            self.cond.notify_all();
        }
    }

    fn at_least(&self, want: u8) -> bool {
        *self.level.lock().unwrap() >= want
    }

    pub(crate) fn wait_at_least(&self, want: u8, timeout: Duration) -> bool {
        let deadline = Instant::now() + timeout;
        let mut level = self.level.lock().unwrap();
        while *level < want {
            let now = Instant::now();
            if now >= deadline {
                return false;
            }
            let (guard, _) = self.cond.wait_timeout(level, deadline - now).unwrap();
            level = guard;
        }
        true
    }
}

/// A parsed tree entry (from a raw `tree` object).
#[derive(Debug, Clone)]
pub(crate) struct RawTreeEntry {
    pub name: String,
    /// Octal mode as stored: `100644`, `100755`, `120000`, `40000`, `160000`.
    pub mode: u32,
    pub oid: String,
}

impl RawTreeEntry {
    pub(crate) fn is_tree(&self) -> bool {
        self.mode & 0o170000 == 0o040000
    }
}

/// Parse a raw git tree object: repeated `<octal mode> <name>\0<20-byte oid>`.
pub(crate) fn parse_tree(data: &[u8]) -> Result<Vec<RawTreeEntry>, String> {
    let mut entries = Vec::new();
    let mut rest = data;
    while !rest.is_empty() {
        let sp = rest
            .iter()
            .position(|&b| b == b' ')
            .ok_or("corrupt tree: no mode terminator")?;
        let mode = std::str::from_utf8(&rest[..sp])
            .ok()
            .and_then(|s| u32::from_str_radix(s, 8).ok())
            .ok_or("corrupt tree: bad mode")?;
        rest = &rest[sp + 1..];
        let nul = rest
            .iter()
            .position(|&b| b == 0)
            .ok_or("corrupt tree: no name terminator")?;
        let name = String::from_utf8_lossy(&rest[..nul]).into_owned();
        rest = &rest[nul + 1..];
        if rest.len() < 20 {
            return Err("corrupt tree: truncated oid".to_string());
        }
        let oid = hex(&rest[..20]);
        rest = &rest[20..];
        entries.push(RawTreeEntry { name, mode, oid });
    }
    Ok(entries)
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// One long-lived `git cat-file --batch-command` child.
struct CatFile {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl CatFile {
    fn spawn(git_dir: &Path) -> Result<CatFile, String> {
        let mut child = git_base(git_dir)
            .args(["cat-file", "--batch-command"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|e| format!("spawn git cat-file: {e}"))?;
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        Ok(CatFile {
            child,
            stdin,
            stdout,
        })
    }

    /// Send one command line, read the header line.
    fn round_trip(&mut self, line: &str) -> Result<String, String> {
        self.stdin
            .write_all(line.as_bytes())
            .and_then(|_| self.stdin.write_all(b"\n"))
            .and_then(|_| self.stdin.flush())
            .map_err(|e| format!("cat-file write: {e}"))?;
        let mut header = String::new();
        self.stdout
            .read_line(&mut header)
            .map_err(|e| format!("cat-file read: {e}"))?;
        if header.is_empty() {
            return Err("cat-file: eof".to_string());
        }
        Ok(header.trim_end().to_string())
    }
}

impl Drop for CatFile {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Object metadata from `info <oid>`.
pub(crate) struct ObjInfo {
    pub kind: String,
    pub size: u64,
}

pub(crate) struct LocalCache {
    git_dir: PathBuf,
    catfile: Mutex<Option<CatFile>>,
    /// One background ref-fetch at a time; extra triggers coalesce.
    fetching: Arc<AtomicBool>,
    /// Serializes every `git fetch` against the cache repo: concurrent
    /// fetches contend on git's own `shallow.lock` and fail (seen when an
    /// on-demand commit fetch raced the warmup's shallow fetch).
    fetch_lock: Arc<Mutex<()>>,
    /// Pids of in-flight `git fetch` children, killed on drop so an
    /// unmount doesn't leave orphaned fetches writing into the cache.
    fetch_pids: Arc<Mutex<HashSet<u32>>>,
    /// Set on drop; stops the warmup retry loop.
    shutdown: Arc<AtomicBool>,
    /// Lazy-history mode: warmup stops at ref tips; history is deepened
    /// only when older commits are actually read.
    lazy_history: bool,
    /// Whether background fetching is enabled at all (`Options::warmup`).
    fetch_enabled: bool,
    /// Commits already requested via [`fetch_commit_async`], so each sha is
    /// fetched at most once per mount.
    requested_commits: Mutex<HashSet<String>>,
    pub(crate) warm: Arc<WarmState>,
}

impl Drop for LocalCache {
    fn drop(&mut self) {
        self.shutdown.store(true, Ordering::SeqCst);
        for pid in self.fetch_pids.lock().unwrap().iter() {
            // SAFETY: plain kill(2) on a child we spawned; worst case the
            // pid was already reaped and the signal goes nowhere valid —
            // acceptable for teardown.
            unsafe { libc::kill(*pid as i32, libc::SIGTERM) };
        }
    }
}

/// Run a git fetch whose pid is registered in `pids` while it runs, so
/// [`LocalCache::drop`] can interrupt it.
fn run_git_fetch(git_dir: &Path, args: &[&str], pids: &Mutex<HashSet<u32>>) -> Result<(), String> {
    let child = git_base(git_dir)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("git {}: {e}", args.join(" ")))?;
    let pid = child.id();
    pids.lock().unwrap().insert(pid);
    let out = child.wait_with_output();
    pids.lock().unwrap().remove(&pid);
    let out = out.map_err(|e| format!("git {}: {e}", args.join(" ")))?;
    if !out.status.success() {
        return Err(format!(
            "git {}: {}",
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(())
}

/// A `git` invocation against the cache repo, isolated from user config.
fn git_base(git_dir: &Path) -> Command {
    let mut cmd = Command::new("git");
    cmd.arg("--git-dir")
        .arg(git_dir)
        .env("GIT_TERMINAL_PROMPT", "0")
        .env_remove("GIT_DIR")
        .env_remove("GIT_WORK_TREE");
    cmd
}

/// Deepen a shallow cache until `commit` is reachable from a mirrored ref,
/// backfilling the history between the shallow boundary and that commit.
/// Doubles the absolute fetch depth each round (git-server supports
/// depth-based shallow only, so "deepen down to <sha>" must be found by
/// search); gives up past `DEEPEN_MAX_DEPTH` — the commit's own snapshot is
/// already pinned, so only connectivity is missing.
fn deepen_until_connected(
    dir: &Path,
    commit: &str,
    fetch_lock: &Mutex<()>,
    fetch_pids: &Mutex<HashSet<u32>>,
    shutdown: &AtomicBool,
) {
    /// First deepening step; doubles each round.
    const DEEPEN_INITIAL_DEPTH: u32 = 64;
    /// Past this depth (2^17 commits of history), stop searching.
    const DEEPEN_MAX_DEPTH: u32 = 1 << 17;
    let started = Instant::now();
    let mut depth = DEEPEN_INITIAL_DEPTH;
    loop {
        if shutdown.load(Ordering::SeqCst) {
            return;
        }
        if !dir.join("shallow").exists() {
            return; // the whole clone is complete; nothing left to deepen
        }
        let connected = run_git(
            dir,
            &[
                "for-each-ref",
                &format!("--contains={commit}"),
                "refs/heads",
                "refs/tags",
            ],
        )
        .map(|out| !out.trim().is_empty())
        .unwrap_or(false);
        if connected {
            vlog!("history deepened to {commit} in {:?}", started.elapsed());
            return;
        }
        if depth > DEEPEN_MAX_DEPTH {
            vlog!("giving up deepening to {commit} (depth {depth} reached)");
            return;
        }
        let arg = format!("--depth={depth}");
        let result = {
            let _serialize = fetch_lock.lock().unwrap();
            run_git_fetch(dir, &["fetch", "--quiet", &arg, "origin"], fetch_pids)
        };
        if let Err(e) = result {
            vlog!("deepening to {commit} failed at depth {depth}: {e}");
            return;
        }
        depth = depth.saturating_mul(2);
    }
}

/// Bounded housekeeping after a successful fetch: `git maintenance run
/// --auto` is a no-op until git's own thresholds trip, then consolidates
/// loose objects/packs so a long-lived cache doesn't degrade (many small
/// packs slow every object lookup) or leak disk. Serialized with fetches
/// and killable on unmount like any other cache-repo child.
fn run_maintenance(git_dir: &Path, fetch_lock: &Mutex<()>, fetch_pids: &Mutex<HashSet<u32>>) {
    let _serialize = fetch_lock.lock().unwrap();
    if let Err(e) = run_git_fetch(
        git_dir,
        &["maintenance", "run", "--auto", "--quiet"],
        fetch_pids,
    ) {
        vlog!("maintenance failed: {e}");
    }
}

/// The remote's default branch (full ref name, e.g. `refs/heads/main`),
/// from the HEAD symref in `git ls-remote` — one cheap ref advertisement.
fn default_branch(git_dir: &Path) -> Result<String, String> {
    let out = run_git(git_dir, &["ls-remote", "--symref", "origin", "HEAD"])?;
    for line in out.lines() {
        // "ref: refs/heads/main\tHEAD"
        if let Some(rest) = line.strip_prefix("ref: ") {
            if let Some((target, _)) = rest.split_once('\t') {
                return Ok(target.trim().to_string());
            }
        }
    }
    Err("ls-remote: no HEAD symref advertised".to_string())
}

fn run_git(git_dir: &Path, args: &[&str]) -> Result<String, String> {
    let out = git_base(git_dir)
        .args(args)
        .output()
        .map_err(|e| format!("git {}: {e}", args.join(" ")))?;
    if !out.status.success() {
        return Err(format!(
            "git {}: {}",
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

impl LocalCache {
    /// Open (creating if needed) the cache repo and, when `warmup`, start the
    /// staged background fetch (shallow default branch, then everything —
    /// or just every tip when `lazy_history`).
    pub(crate) fn open(
        dir: &Path,
        remote_url: &str,
        warmup: bool,
        lazy_history: bool,
    ) -> Result<LocalCache, String> {
        if !dir.join("HEAD").exists() {
            std::fs::create_dir_all(dir).map_err(|e| format!("create {}: {e}", dir.display()))?;
            run_git(dir, &["init", "--bare", "--quiet"])?;
        }
        // (Re)point origin at the remote. The refspec mirrors branches and
        // tags — deliberately not refs/* — so the private refs/git-fuse/
        // namespace (keep-refs pinning on-demand fetches) can never be
        // removed by a pruning fetch.
        run_git(dir, &["config", "remote.origin.url", remote_url])?;
        run_git(
            dir,
            &[
                "config",
                "--replace-all",
                "remote.origin.fetch",
                "+refs/heads/*:refs/heads/*",
            ],
        )?;
        run_git(
            dir,
            &[
                "config",
                "--add",
                "remote.origin.fetch",
                "+refs/tags/*:refs/tags/*",
            ],
        )?;

        let cache = LocalCache {
            git_dir: dir.to_path_buf(),
            catfile: Mutex::new(None),
            fetching: Arc::new(AtomicBool::new(false)),
            fetch_lock: Arc::new(Mutex::new(())),
            fetch_pids: Arc::new(Mutex::new(HashSet::new())),
            shutdown: Arc::new(AtomicBool::new(false)),
            lazy_history,
            fetch_enabled: warmup,
            requested_commits: Mutex::new(HashSet::new()),
            warm: WarmState::new(),
        };

        // A pre-existing non-shallow cache with mirrored refs is already
        // warm: serve from it immediately and let the incremental fetch
        // find new pushes. (Keep-refs don't count — they exist even when
        // the mirror stages never ran.)
        let has_refs = run_git(
            dir,
            &["for-each-ref", "--count=1", "refs/heads", "refs/tags"],
        )
        .map(|s| !s.trim().is_empty())
        .unwrap_or(false);
        let is_shallow = dir.join("shallow").exists();
        if has_refs {
            cache.warm.advance(STATE_SHALLOW);
            if !is_shallow {
                cache.warm.advance(STATE_WARM);
            }
        }

        if warmup {
            cache.spawn_warmup();
        }
        Ok(cache)
    }

    fn spawn_warmup(&self) {
        let dir = self.git_dir.clone();
        let warm = self.warm.clone();
        let fetching = self.fetching.clone();
        let fetch_lock = self.fetch_lock.clone();
        let fetch_pids = self.fetch_pids.clone();
        let shutdown = self.shutdown.clone();
        let lazy_history = self.lazy_history;
        std::thread::Builder::new()
            .name("git-fuse-warmup".to_string())
            .spawn(move || {
                // The cache must converge to a complete mirror (all refs,
                // full history) as long as the mount lives: retry failed
                // stages with capped backoff until STATE_WARM is reached.
                // Reads never wait on this loop — they are served from the
                // remote API until the objects land.
                let mut backoff = WARMUP_RETRY_INITIAL;
                let started = Instant::now();
                loop {
                    if shutdown.load(Ordering::SeqCst) {
                        return;
                    }
                    fetching.store(true, Ordering::SeqCst);
                    // Stage 1: shallow fetch of the default branch only — the
                    // cheapest fetch that makes the trees and blobs almost
                    // every read wants first local. (A repo like kubernetes
                    // has dozens of release branches; their tips would
                    // multiply this stage.)
                    if !warm.at_least(STATE_SHALLOW) {
                        match default_branch(dir.as_path()) {
                            Ok(branch) => {
                                let refspec = format!("+{branch}:{branch}");
                                let stage1 = {
                                    let _serialize = fetch_lock.lock().unwrap();
                                    run_git_fetch(
                                        dir.as_path(),
                                        &["fetch", "--quiet", "--depth=1", "origin", &refspec],
                                        &fetch_pids,
                                    )
                                };
                                match stage1 {
                                    Ok(_) => {
                                        // Point the cache's HEAD at the same
                                        // branch so local ref resolution
                                        // matches the remote.
                                        let _ = run_git(
                                            dir.as_path(),
                                            &["symbolic-ref", "HEAD", &branch],
                                        );
                                        warm.advance(STATE_SHALLOW);
                                        vlog!(
                                            "shallow fetch of {branch} done in {:?}",
                                            started.elapsed()
                                        );
                                    }
                                    Err(e) => vlog!("shallow fetch of {branch} failed: {e}"),
                                }
                            }
                            Err(e) => vlog!("default-branch discovery failed: {e}"),
                        }
                    }
                    // Stage 2: all mirrored refs. Eager (default): full
                    // history via --unshallow. Lazy: just every tip at
                    // depth 1 — history arrives only when it's read. Either
                    // way, an already-complete cache gets a plain
                    // incremental fetch (a --depth fetch would re-shallow
                    // it, throwing away completeness a previous eager mount
                    // paid for).
                    let full = {
                        let _serialize = fetch_lock.lock().unwrap();
                        let is_shallow = dir.join("shallow").exists();
                        // Refs but no shallow file = a complete mirror from
                        // an earlier eager mount.
                        let is_complete = !is_shallow
                            && run_git(
                                dir.as_path(),
                                &["for-each-ref", "--count=1", "refs/heads", "refs/tags"],
                            )
                            .map(|s| !s.trim().is_empty())
                            .unwrap_or(false);
                        let args: &[&str] = if is_complete {
                            &["fetch", "--quiet", "origin"]
                        } else if lazy_history {
                            &["fetch", "--quiet", "--depth=1", "origin"]
                        } else if is_shallow {
                            &["fetch", "--quiet", "--unshallow", "origin"]
                        } else {
                            &["fetch", "--quiet", "origin"]
                        };
                        run_git_fetch(dir.as_path(), args, &fetch_pids)
                    };
                    fetching.store(false, Ordering::SeqCst);
                    match full {
                        Ok(_) => {
                            warm.advance(STATE_SHALLOW);
                            warm.advance(STATE_WARM);
                            vlog!("full fetch done in {:?}", started.elapsed());
                            run_maintenance(dir.as_path(), &fetch_lock, &fetch_pids);
                            return;
                        }
                        Err(e) => vlog!("full fetch failed (retrying in {backoff:?}): {e}"),
                    }
                    // Back off, waking early on shutdown.
                    let wait_until = Instant::now() + backoff;
                    while Instant::now() < wait_until {
                        if shutdown.load(Ordering::SeqCst) {
                            return;
                        }
                        std::thread::sleep(WARMUP_SHUTDOWN_POLL);
                    }
                    backoff = (backoff * 2).min(WARMUP_RETRY_MAX);
                }
            })
            .expect("spawn warmup thread");
    }

    /// Fetch one commit (and its reachable objects, shallow) in the
    /// background, so a read that had to fall through to the remote API —
    /// another branch, old history, a dangling sha — is local next time.
    /// Each sha is requested at most once per mount; requires the server to
    /// accept sha wants (git-server does; plain git needs
    /// `uploadpack.allowAnySHA1InWant`). Failures are logged and ignored:
    /// the remote API keeps serving the content either way.
    pub(crate) fn fetch_commit_async(&self, commit: &str) {
        if !self.fetch_enabled
            || !self
                .requested_commits
                .lock()
                .unwrap()
                .insert(commit.to_string())
        {
            return;
        }
        let dir = self.git_dir.clone();
        let commit = commit.to_string();
        let fetch_lock = self.fetch_lock.clone();
        let fetch_pids = self.fetch_pids.clone();
        let shutdown = self.shutdown.clone();
        let lazy_history = self.lazy_history;
        std::thread::Builder::new()
            .name("git-fuse-fetch-commit".to_string())
            .spawn(move || {
                let started = Instant::now();
                let already_local = {
                    let _serialize = fetch_lock.lock().unwrap();
                    // A fetch that finished while we waited (say, the
                    // warmup's shallow stage) may have landed it already.
                    if run_git(dir.as_path(), &["cat-file", "-e", &commit]).is_ok() {
                        true
                    } else {
                        match run_git_fetch(
                            dir.as_path(),
                            &["fetch", "--quiet", "--depth=1", "origin", &commit],
                            &fetch_pids,
                        ) {
                            Ok(_) => {
                                // Pin the commit with a keep-ref: `fetch
                                // <sha>` stores objects unreachable from any
                                // ref, and git's auto-gc would prune them
                                // again after pruneExpire.
                                let keep = format!("refs/git-fuse/keep/{commit}");
                                if let Err(e) =
                                    run_git(dir.as_path(), &["update-ref", &keep, &commit])
                                {
                                    vlog!("keep-ref for {commit} failed: {e}");
                                }
                                vlog!(
                                    "on-demand fetch of {commit} done in {:?}",
                                    started.elapsed()
                                );
                                false
                            }
                            Err(e) => {
                                vlog!("on-demand fetch of {commit} failed: {e}");
                                return;
                            }
                        }
                    }
                };
                // Lazy mode backfills on access: after the snapshot lands,
                // deepen the shallow clone until this commit connects to
                // the ref tips, so the intervening history becomes local
                // too. (Eager mode has, or will have, full history from the
                // warmup; only dangling commits reach this path there, and
                // no amount of deepening connects those.)
                if lazy_history && !already_local {
                    deepen_until_connected(
                        dir.as_path(),
                        &commit,
                        &fetch_lock,
                        &fetch_pids,
                        &shutdown,
                    );
                }
            })
            .expect("spawn commit fetch thread");
    }

    /// Kick one incremental `git fetch` on a background thread (no-op when a
    /// fetch is already running). Called when the ref refresh sees new heads.
    pub(crate) fn fetch_async(&self) {
        if !self.fetch_enabled {
            return;
        }
        if self
            .fetching
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_err()
        {
            return;
        }
        let dir = self.git_dir.clone();
        let fetching = self.fetching.clone();
        let fetch_lock = self.fetch_lock.clone();
        let fetch_pids = self.fetch_pids.clone();
        std::thread::Builder::new()
            .name("git-fuse-fetch".to_string())
            .spawn(move || {
                let started = Instant::now();
                let result = {
                    let _serialize = fetch_lock.lock().unwrap();
                    run_git_fetch(
                        dir.as_path(),
                        &["fetch", "--quiet", "--prune", "origin"],
                        &fetch_pids,
                    )
                };
                match result {
                    Ok(_) => {
                        vlog!("incremental fetch done in {:?}", started.elapsed());
                        run_maintenance(dir.as_path(), &fetch_lock, &fetch_pids);
                    }
                    Err(e) => vlog!("incremental fetch failed: {e}"),
                }
                fetching.store(false, Ordering::SeqCst);
            })
            .expect("spawn fetch thread");
    }

    /// Run `f` with a live cat-file child, respawning once if it died.
    fn with_catfile<T>(&self, f: impl Fn(&mut CatFile) -> Result<T, String>) -> Result<T, String> {
        let mut guard = self.catfile.lock().unwrap();
        for _ in 0..2 {
            if guard.is_none() {
                *guard = Some(CatFile::spawn(&self.git_dir)?);
            }
            match f(guard.as_mut().unwrap()) {
                Ok(v) => return Ok(v),
                Err(_) => *guard = None, // child died; respawn and retry once
            }
        }
        Err("cat-file: child kept dying".to_string())
    }

    /// Object type and size, or `None` when the object isn't local (yet).
    pub(crate) fn info(&self, oid: &str) -> Result<Option<ObjInfo>, String> {
        self.with_catfile(|cf| {
            let header = cf.round_trip(&format!("info {oid}"))?;
            Ok(parse_header(&header))
        })
    }

    /// Batched `info` for many oids: all commands are written first, then
    /// all replies read — one pipe flush instead of one round trip per oid.
    /// Order matches the input.
    pub(crate) fn infos(&self, oids: &[&str]) -> Result<Vec<Option<ObjInfo>>, String> {
        if oids.is_empty() {
            return Ok(Vec::new());
        }
        self.with_catfile(|cf| {
            let mut commands = String::with_capacity(oids.len() * 46);
            for oid in oids {
                commands.push_str("info ");
                commands.push_str(oid);
                commands.push('\n');
            }
            cf.stdin
                .write_all(commands.as_bytes())
                .and_then(|_| cf.stdin.flush())
                .map_err(|e| format!("cat-file write: {e}"))?;
            let mut out = Vec::with_capacity(oids.len());
            for _ in oids {
                let mut header = String::new();
                cf.stdout
                    .read_line(&mut header)
                    .map_err(|e| format!("cat-file read: {e}"))?;
                if header.is_empty() {
                    return Err("cat-file: eof".to_string());
                }
                out.push(parse_header(header.trim_end()));
            }
            Ok(out)
        })
    }

    /// Full object contents, or `None` when the object isn't local (yet).
    pub(crate) fn contents(&self, oid: &str) -> Result<Option<(String, Vec<u8>)>, String> {
        self.with_catfile(|cf| {
            let header = cf.round_trip(&format!("contents {oid}"))?;
            let Some(info) = parse_header(&header) else {
                return Ok(None);
            };
            let mut data = vec![0u8; info.size as usize];
            cf.stdout
                .read_exact(&mut data)
                .map_err(|e| format!("cat-file body: {e}"))?;
            let mut nl = [0u8; 1];
            cf.stdout
                .read_exact(&mut nl)
                .map_err(|e| format!("cat-file trailer: {e}"))?;
            Ok(Some((info.kind, data)))
        })
    }

    /// The `tree` oid of a local commit, peeling annotated tags (so
    /// `commits/<tag-sha>` behaves the same whether served locally or by
    /// the remote API, which also peels). `None` when the object isn't
    /// local.
    pub(crate) fn commit_tree(&self, commit: &str) -> Result<Option<String>, String> {
        /// Nested-tag chains deeper than this are corrupt in practice.
        const MAX_TAG_CHAIN: usize = 10;
        let mut oid = commit.to_string();
        for _ in 0..MAX_TAG_CHAIN {
            let Some((kind, data)) = self.contents(&oid)? else {
                return Ok(None);
            };
            let text = String::from_utf8_lossy(&data);
            match kind.as_str() {
                "commit" => {
                    for line in text.lines() {
                        if let Some(t) = line.strip_prefix("tree ") {
                            return Ok(Some(t.trim().to_string()));
                        }
                    }
                    return Err(format!("corrupt commit {oid}: no tree"));
                }
                "tag" => {
                    let Some(target) = text.lines().find_map(|line| line.strip_prefix("object "))
                    else {
                        return Err(format!("corrupt tag {oid}: no object"));
                    };
                    oid = target.trim().to_string();
                }
                other => {
                    return Err(format!("object {oid} is a {other}, not a commit"));
                }
            }
        }
        Err(format!("object {commit}: tag chain too deep"))
    }

    /// Local ref snapshot (`for-each-ref` + HEAD symref) for when the remote
    /// API is unreachable.
    pub(crate) fn local_refs(
        &self,
    ) -> Result<(String, std::collections::BTreeMap<String, String>), String> {
        let head = run_git(&self.git_dir, &["symbolic-ref", "--quiet", "HEAD"])
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|_| "refs/heads/main".to_string());
        // Scoped to the mirrored namespaces: private refs/git-fuse/ keep-refs
        // must not leak into the /refs listing.
        let out = run_git(
            &self.git_dir,
            &[
                "for-each-ref",
                "--format=%(objectname) %(refname)",
                "refs/heads",
                "refs/tags",
            ],
        )?;
        let mut refs = std::collections::BTreeMap::new();
        for line in out.lines() {
            if let Some((oid, name)) = line.split_once(' ') {
                refs.insert(name.to_string(), oid.to_string());
            }
        }
        Ok((head, refs))
    }
}

/// Parse a `cat-file --batch-command` header: `<oid> <type> <size>`, or
/// `<oid> missing` / `<oid> ambiguous` → `None`.
fn parse_header(header: &str) -> Option<ObjInfo> {
    let mut parts = header.split(' ');
    let _oid = parts.next()?;
    let kind = parts.next()?;
    if kind == "missing" || kind == "ambiguous" {
        return None;
    }
    let size: u64 = parts.next()?.parse().ok()?;
    Some(ObjInfo {
        kind: kind.to_string(),
        size,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tree_parsing() {
        // Build a two-entry tree: a blob "a.txt" and a subtree "dir".
        let mut raw = Vec::new();
        raw.extend_from_slice(b"100644 a.txt\0");
        raw.extend_from_slice(&[0xab; 20]);
        raw.extend_from_slice(b"40000 dir\0");
        raw.extend_from_slice(&[0xcd; 20]);
        let entries = parse_tree(&raw).unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].name, "a.txt");
        assert_eq!(entries[0].mode, 0o100644);
        assert!(!entries[0].is_tree());
        assert_eq!(entries[0].oid, "ab".repeat(20));
        assert_eq!(entries[1].name, "dir");
        assert!(entries[1].is_tree());

        assert!(parse_tree(b"garbage").is_err());
        assert!(parse_tree(&raw[..raw.len() - 1]).is_err());
    }

    #[test]
    fn header_parsing() {
        let info = parse_header("abc123 blob 42").unwrap();
        assert_eq!(info.kind, "blob");
        assert_eq!(info.size, 42);
        assert!(parse_header("abc123 missing").is_none());
        assert!(parse_header("").is_none());
    }
}
