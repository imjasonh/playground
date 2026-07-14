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
//! 1. **shallow** — `git fetch --depth=1` of all refs (tip trees + blobs);
//! 2. **full** — `git fetch --unshallow` (complete history).
//!
//! Both run on a background thread; [`WarmState`] tracks progress so callers
//! (and tests) can wait for a stage. When the ref refresh notices new remote
//! heads, [`LocalCache::fetch_async`] runs one incremental fetch at a time.

use crate::vlog;
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
    /// One background fetch at a time; extra triggers coalesce.
    fetching: Arc<AtomicBool>,
    pub(crate) warm: Arc<WarmState>,
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
    /// shallow→full background fetch.
    pub(crate) fn open(dir: &Path, remote_url: &str, warmup: bool) -> Result<LocalCache, String> {
        if !dir.join("HEAD").exists() {
            std::fs::create_dir_all(dir).map_err(|e| format!("create {}: {e}", dir.display()))?;
            run_git(dir, &["init", "--bare", "--quiet"])?;
        }
        // (Re)point origin at the remote; the refspec mirrors every ref so
        // the cache can serve any branch or tag.
        run_git(dir, &["config", "remote.origin.url", remote_url])?;
        run_git(dir, &["config", "remote.origin.fetch", "+refs/*:refs/*"])?;

        let cache = LocalCache {
            git_dir: dir.to_path_buf(),
            catfile: Mutex::new(None),
            fetching: Arc::new(AtomicBool::new(false)),
            warm: WarmState::new(),
        };

        // A pre-existing non-shallow cache with refs is already warm: serve
        // from it immediately and let the incremental fetch find new pushes.
        let has_refs = run_git(dir, &["for-each-ref", "--count=1"])
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
        std::thread::Builder::new()
            .name("git-fuse-warmup".to_string())
            .spawn(move || {
                fetching.store(true, Ordering::SeqCst);
                let started = Instant::now();
                // Stage 1: shallow — the cheapest fetch that makes tip trees
                // and blobs local.
                match run_git(dir.as_path(), &["fetch", "--quiet", "--depth=1", "origin"]) {
                    Ok(_) => {
                        warm.advance(STATE_SHALLOW);
                        vlog!("shallow fetch done in {:?}", started.elapsed());
                    }
                    Err(e) => vlog!("shallow fetch failed: {e}"),
                }
                // Stage 2: full history.
                let full = if dir.join("shallow").exists() {
                    run_git(
                        dir.as_path(),
                        &["fetch", "--quiet", "--unshallow", "origin"],
                    )
                } else {
                    run_git(dir.as_path(), &["fetch", "--quiet", "origin"])
                };
                match full {
                    Ok(_) => {
                        warm.advance(STATE_SHALLOW);
                        warm.advance(STATE_WARM);
                        vlog!("full fetch done in {:?}", started.elapsed());
                    }
                    Err(e) => vlog!("full fetch failed: {e}"),
                }
                fetching.store(false, Ordering::SeqCst);
            })
            .expect("spawn warmup thread");
    }

    /// Kick one incremental `git fetch` on a background thread (no-op when a
    /// fetch is already running). Called when the ref refresh sees new heads.
    pub(crate) fn fetch_async(&self) {
        if self
            .fetching
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_err()
        {
            return;
        }
        let dir = self.git_dir.clone();
        let fetching = self.fetching.clone();
        std::thread::Builder::new()
            .name("git-fuse-fetch".to_string())
            .spawn(move || {
                let started = Instant::now();
                match run_git(dir.as_path(), &["fetch", "--quiet", "--prune", "origin"]) {
                    Ok(_) => vlog!("incremental fetch done in {:?}", started.elapsed()),
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

    /// The `tree` oid of a local commit, or `None` when the commit isn't
    /// local.
    pub(crate) fn commit_tree(&self, commit: &str) -> Result<Option<String>, String> {
        let Some((kind, data)) = self.contents(commit)? else {
            return Ok(None);
        };
        if kind != "commit" {
            return Err(format!("object {commit} is a {kind}, not a commit"));
        }
        let text = String::from_utf8_lossy(&data);
        for line in text.lines() {
            if let Some(t) = line.strip_prefix("tree ") {
                return Ok(Some(t.trim().to_string()));
            }
        }
        Err(format!("corrupt commit {commit}: no tree"))
    }

    /// Local ref snapshot (`for-each-ref` + HEAD symref) for when the remote
    /// API is unreachable.
    pub(crate) fn local_refs(
        &self,
    ) -> Result<(String, std::collections::BTreeMap<String, String>), String> {
        let head = run_git(&self.git_dir, &["symbolic-ref", "--quiet", "HEAD"])
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|_| "refs/heads/main".to_string());
        let out = run_git(
            &self.git_dir,
            &["for-each-ref", "--format=%(objectname) %(refname)"],
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
