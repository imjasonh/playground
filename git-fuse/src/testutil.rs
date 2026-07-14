//! Test/bench harness: a localhost server that looks like git-server.
//!
//! It serves a real bare repository over both surfaces git-fuse consumes:
//!
//! * **git smart-HTTP** (`/info/refs`, `/git-upload-pack`) via the
//!   `git http-backend` CGI shipped with git — real protocol-v2 fetches,
//!   including shallow and `--unshallow`;
//! * the **JSON read API** (`/api/<repo>/refs`, `/tree/…`, `/file/…`) shaped
//!   exactly like git-server's (`git-server/docs/api.md`), implemented with
//!   git plumbing.
//!
//! Living in the crate (rather than `tests/common/`) lets benchmarks share
//! it: bench targets cannot import test modules.
//!
//! Knobs for tests and benches: per-request artificial latency (simulate a
//! far-away server), failing either surface (prove reads survive without
//! the other), and per-category request counters.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// True when this host can actually mount FUSE filesystems. e2e tests skip
/// (loudly) when it can't, so the suite still passes in containers without
/// `/dev/fuse`.
pub fn fuse_available() -> bool {
    if !Path::new("/dev/fuse").exists() {
        return false;
    }
    ["fusermount3", "fusermount"].iter().any(|bin| {
        Command::new(bin)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok()
    })
}

/// Exempt loopback from any HTTP proxy the host environment configures
/// (CI VMs often set a global `http.proxy` for egress). libcurl — and
/// therefore the `git fetch`es the cache runs — honors `no_proxy` even when
/// a proxy comes from git config. Called by every fixture constructor.
fn no_proxy_for_loopback() {
    for key in ["NO_PROXY", "no_proxy"] {
        let mut value = std::env::var(key).unwrap_or_default();
        if !value.contains("127.0.0.1") {
            if !value.is_empty() {
                value.push(',');
            }
            value.push_str("127.0.0.1,localhost");
            std::env::set_var(key, value);
        }
    }
}

/// Minimal scoped temp dir (avoids promoting `tempfile` to a full
/// dependency just for the harness).
pub struct TempDir {
    path: PathBuf,
}

static TEMP_SEQ: AtomicU64 = AtomicU64::new(0);

impl TempDir {
    pub fn new(label: &str) -> TempDir {
        let path = std::env::temp_dir().join(format!(
            "git-fuse-{label}-{}-{}",
            std::process::id(),
            TEMP_SEQ.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).expect("create temp dir");
        TempDir { path }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// One file operation for [`TestRepo::commit`].
pub enum Spec<'a> {
    File(&'a str, &'a [u8]),
    Exec(&'a str, &'a [u8]),
    Symlink(&'a str, &'a str),
    Remove(&'a str),
}

/// A bare upstream repository plus a working clone to author commits in.
pub struct TestRepo {
    root: TempDir,
    bare: PathBuf,
    work: PathBuf,
}

fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .current_dir(dir)
        .args(args)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .env("GIT_AUTHOR_NAME", "test")
        .env("GIT_AUTHOR_EMAIL", "test@example.com")
        .env("GIT_COMMITTER_NAME", "test")
        .env("GIT_COMMITTER_EMAIL", "test@example.com")
        .env("GIT_TERMINAL_PROMPT", "0")
        .output()
        .unwrap_or_else(|e| panic!("git {}: {e}", args.join(" ")));
    assert!(
        out.status.success(),
        "git {} failed: {}",
        args.join(" "),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

impl TestRepo {
    pub fn new() -> TestRepo {
        no_proxy_for_loopback();
        let root = TempDir::new("repo");
        let bare = root.path().join("repo");
        let work = root.path().join("work");
        std::fs::create_dir_all(&bare).unwrap();
        std::fs::create_dir_all(&work).unwrap();
        git(&bare, &["init", "--bare", "--quiet", "-b", "main"]);
        git(&work, &["init", "--quiet", "-b", "main"]);
        git(
            &work,
            &["remote", "add", "origin", bare.to_str().unwrap()],
        );
        TestRepo { root, bare, work }
    }

    /// The bare repo directory the server serves.
    pub fn bare(&self) -> &Path {
        &self.bare
    }

    /// Apply `specs` in the work tree, commit, and push `main`. Returns the
    /// new commit sha.
    pub fn commit(&self, message: &str, specs: &[Spec<'_>]) -> String {
        for spec in specs {
            match spec {
                Spec::File(path, contents) | Spec::Exec(path, contents) => {
                    let full = self.work.join(path);
                    if let Some(parent) = full.parent() {
                        std::fs::create_dir_all(parent).unwrap();
                    }
                    std::fs::write(&full, contents).unwrap();
                    if matches!(spec, Spec::Exec(..)) {
                        git(&self.work, &["update-index", "--add", "--chmod=+x", path]);
                        #[cfg(unix)]
                        {
                            use std::os::unix::fs::PermissionsExt;
                            std::fs::set_permissions(
                                &full,
                                std::fs::Permissions::from_mode(0o755),
                            )
                            .unwrap();
                        }
                    }
                }
                Spec::Symlink(path, target) => {
                    let full = self.work.join(path);
                    if let Some(parent) = full.parent() {
                        std::fs::create_dir_all(parent).unwrap();
                    }
                    let _ = std::fs::remove_file(&full);
                    #[cfg(unix)]
                    std::os::unix::fs::symlink(target, &full).unwrap();
                }
                Spec::Remove(path) => {
                    let _ = std::fs::remove_file(self.work.join(path));
                }
            }
        }
        git(&self.work, &["add", "-A"]);
        git(&self.work, &["commit", "--quiet", "-m", message]);
        git(&self.work, &["push", "--quiet", "origin", "main"]);
        self.rev_parse("HEAD")
    }

    /// Tag the current head and push the tag.
    pub fn tag(&self, name: &str) {
        git(&self.work, &["tag", name]);
        git(
            &self.work,
            &["push", "--quiet", "origin", &format!("refs/tags/{name}")],
        );
    }

    /// Push the current head as a new branch.
    pub fn branch(&self, name: &str) {
        git(
            &self.work,
            &[
                "push",
                "--quiet",
                "origin",
                &format!("HEAD:refs/heads/{name}"),
            ],
        );
    }

    /// Commit a gitlink (submodule pointer) at `path` pointing at `sha`,
    /// push main, and return the new commit.
    pub fn commit_gitlink(&self, path: &str, sha: &str, message: &str) -> String {
        git(
            &self.work,
            &[
                "update-index",
                "--add",
                "--cacheinfo",
                &format!("160000,{sha},{path}"),
            ],
        );
        git(&self.work, &["commit", "--quiet", "-m", message]);
        git(&self.work, &["push", "--quiet", "origin", "main"]);
        self.rev_parse("HEAD")
    }

    /// Resolve a refish against the upstream bare repo.
    pub fn rev_parse(&self, refish: &str) -> String {
        git(&self.bare, &["rev-parse", "--verify", refish])
            .trim()
            .to_string()
    }

    /// `git ls-tree -r` of a commit in the upstream, as `path` → oid — the
    /// ground truth for traversal tests.
    pub fn ls_tree_recursive(&self, commit: &str) -> Vec<(String, String)> {
        git(&self.bare, &["ls-tree", "-r", "-z", commit])
            .split('\0')
            .filter(|l| !l.is_empty())
            .map(|line| {
                let (meta, name) = line.split_once('\t').expect("ls-tree line");
                let oid = meta.split(' ').nth(2).expect("ls-tree oid");
                (name.to_string(), oid.to_string())
            })
            .collect()
    }

    /// File contents at a commit, from the upstream (ground truth).
    pub fn show(&self, commit: &str, path: &str) -> Vec<u8> {
        let out = Command::new("git")
            .current_dir(&self.bare)
            .args(["cat-file", "blob", &format!("{commit}:{path}")])
            .output()
            .expect("git cat-file");
        assert!(out.status.success(), "cat-file {commit}:{path} failed");
        out.stdout
    }

    /// Keep the root temp dir alive as long as the repo.
    pub fn root(&self) -> &Path {
        self.root.path()
    }
}

impl Default for TestRepo {
    fn default() -> Self {
        Self::new()
    }
}

/// Request categories counted by the server.
pub const CAT_SMART: &str = "smart";
pub const CAT_API_REFS: &str = "api_refs";
pub const CAT_API_TREE: &str = "api_tree";
pub const CAT_API_FILE: &str = "api_file";

struct ServerState {
    bare: PathBuf,
    delay_ms: AtomicU64,
    fail_smart: AtomicBool,
    fail_api: AtomicBool,
    counts: Mutex<HashMap<&'static str, u64>>,
}

/// A running localhost git-server lookalike.
pub struct TestServer {
    server: Arc<tiny_http::Server>,
    state: Arc<ServerState>,
    port: u16,
    workers: Vec<std::thread::JoinHandle<()>>,
}

impl TestServer {
    /// Serve `repo`'s bare directory as `http://127.0.0.1:<port>/repo`.
    pub fn start(repo: &TestRepo) -> TestServer {
        let server =
            Arc::new(tiny_http::Server::http("127.0.0.1:0").expect("bind test server"));
        let port = server.server_addr().to_ip().unwrap().port();
        let state = Arc::new(ServerState {
            bare: repo.bare().to_path_buf(),
            delay_ms: AtomicU64::new(0),
            fail_smart: AtomicBool::new(false),
            fail_api: AtomicBool::new(false),
            counts: Mutex::new(HashMap::new()),
        });
        // Several workers so a long smart-HTTP fetch can't starve API reads
        // (the startup race depends on both being served concurrently).
        let workers = (0..4)
            .map(|_| {
                let server = server.clone();
                let state = state.clone();
                std::thread::spawn(move || {
                    while let Ok(req) = server.recv() {
                        handle(&state, req);
                    }
                })
            })
            .collect();
        TestServer {
            server,
            state,
            port,
            workers,
        }
    }

    /// The clone URL (also what `git_fuse::Options::new` takes).
    pub fn url(&self) -> String {
        format!("http://127.0.0.1:{}/repo", self.port)
    }

    /// Add artificial latency to every request (simulates a distant server).
    pub fn set_delay(&self, delay: Duration) {
        self.state
            .delay_ms
            .store(delay.as_millis() as u64, Ordering::Relaxed);
    }

    /// Make smart-HTTP endpoints fail (warmup fetches can't progress).
    pub fn set_fail_smart(&self, fail: bool) {
        self.state.fail_smart.store(fail, Ordering::Relaxed);
    }

    /// Make the JSON API fail (reads must come from the local cache).
    pub fn set_fail_api(&self, fail: bool) {
        self.state.fail_api.store(fail, Ordering::Relaxed);
    }

    /// How many requests of one category (`CAT_*`) have been served.
    pub fn count(&self, category: &str) -> u64 {
        *self
            .state
            .counts
            .lock()
            .unwrap()
            .get(category)
            .unwrap_or(&0)
    }
}

impl Drop for TestServer {
    fn drop(&mut self) {
        // unblock() wakes exactly one thread stuck in recv(); issue one per
        // worker or the join below deadlocks.
        for _ in 0..self.workers.len() {
            self.server.unblock();
        }
        for w in self.workers.drain(..) {
            let _ = w.join();
        }
    }
}

fn bump(state: &ServerState, category: &'static str) {
    *state.counts.lock().unwrap().entry(category).or_insert(0) += 1;
}

fn respond_error(req: tiny_http::Request, status: u16, msg: &str) {
    let body = format!("{{\"error\": {:?}}}", msg);
    let _ = req.respond(
        tiny_http::Response::from_string(body)
            .with_status_code(status)
            .with_header(
                tiny_http::Header::from_bytes(&b"Content-Type"[..], &b"application/json"[..])
                    .unwrap(),
            ),
    );
}

fn handle(state: &ServerState, req: tiny_http::Request) {
    let trace = std::env::var_os("GIT_FUSE_TEST_TRACE").is_some();
    let started = std::time::Instant::now();
    if trace {
        eprintln!("[testserver] >> {} {}", req.method(), req.url());
    }
    let delay = state.delay_ms.load(Ordering::Relaxed);
    if delay > 0 {
        std::thread::sleep(Duration::from_millis(delay));
    }
    let url = req.url().to_string();
    struct TraceGuard(bool, String, std::time::Instant);
    impl Drop for TraceGuard {
        fn drop(&mut self) {
            if self.0 {
                eprintln!("[testserver] << {} ({:?})", self.1, self.2.elapsed());
            }
        }
    }
    let _guard = TraceGuard(trace, url.clone(), started);
    let (path, query) = url.split_once('?').unwrap_or((url.as_str(), ""));
    let segments: Vec<String> = path
        .split('/')
        .filter(|s| !s.is_empty())
        .map(percent_decode)
        .collect();
    let segs: Vec<&str> = segments.iter().map(|s| s.as_str()).collect();
    match segs.as_slice() {
        ["api", rest @ ..] => {
            if state.fail_api.load(Ordering::Relaxed) {
                respond_error(req, 500, "api disabled by test");
                return;
            }
            handle_api(state, req, rest);
        }
        [_repo, "info", "refs"] | [_repo, "git-upload-pack"] => {
            bump(state, CAT_SMART);
            if state.fail_smart.load(Ordering::Relaxed) {
                respond_error(req, 500, "smart-http disabled by test");
                return;
            }
            let path = path.to_string();
            let query = query.to_string();
            handle_smart(state, req, &path, &query);
        }
        _ => respond_error(req, 404, "not found"),
    }
}

fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            if let Ok(b) = u8::from_str_radix(&s[i + 1..i + 3], 16) {
                out.push(b);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// Run git against the served bare repo; `Ok` is stdout.
fn repo_git(state: &ServerState, args: &[&str]) -> Result<Vec<u8>, String> {
    let out = Command::new("git")
        .current_dir(&state.bare)
        .args(args)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .output()
        .map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(String::from_utf8_lossy(&out.stderr).into_owned());
    }
    Ok(out.stdout)
}

/// Resolve a refish exactly like git-server does: full oid, HEAD, branch,
/// tag, then full ref name (`docs/api.md`).
fn resolve_refish(state: &ServerState, refish: &str) -> Option<String> {
    let candidates: Vec<String> = if refish.len() == 40
        && refish.bytes().all(|b| b.is_ascii_hexdigit())
    {
        vec![refish.to_string()]
    } else if refish == "HEAD" {
        vec!["HEAD".to_string()]
    } else {
        vec![
            format!("refs/heads/{refish}"),
            format!("refs/tags/{refish}"),
            refish.to_string(),
        ]
    };
    for cand in candidates {
        if let Ok(out) = repo_git(
            state,
            &["rev-parse", "--verify", "--quiet", &format!("{cand}^{{commit}}")],
        ) {
            let sha = String::from_utf8_lossy(&out).trim().to_string();
            if !sha.is_empty() {
                return Some(sha);
            }
        }
    }
    None
}

fn json_response(req: tiny_http::Request, body: String) {
    let _ = req.respond(
        tiny_http::Response::from_string(body).with_header(
            tiny_http::Header::from_bytes(&b"Content-Type"[..], &b"application/json"[..])
                .unwrap(),
        ),
    );
}

fn handle_api(state: &ServerState, req: tiny_http::Request, rest: &[&str]) {
    match rest {
        [_repo, "refs"] => {
            bump(state, CAT_API_REFS);
            let head = repo_git(state, &["symbolic-ref", "--quiet", "HEAD"])
                .map(|o| String::from_utf8_lossy(&o).trim().to_string())
                .unwrap_or_else(|_| "refs/heads/main".to_string());
            let refs = repo_git(
                state,
                &["for-each-ref", "--format=%(objectname) %(refname)"],
            )
            .unwrap_or_default();
            let mut map = serde_json::Map::new();
            for line in String::from_utf8_lossy(&refs).lines() {
                if let Some((oid, name)) = line.split_once(' ') {
                    map.insert(name.to_string(), serde_json::Value::String(oid.to_string()));
                }
            }
            let body = serde_json::json!({ "head": head, "refs": map });
            json_response(req, body.to_string());
        }
        [_repo, "tree", refish, path @ ..] => {
            bump(state, CAT_API_TREE);
            let path = path.join("/");
            let Some(commit) = resolve_refish(state, refish) else {
                respond_error(req, 404, &format!("unknown ref {refish}"));
                return;
            };
            let expr = if path.is_empty() {
                format!("{commit}^{{tree}}")
            } else {
                format!("{commit}:{path}")
            };
            let is_tree = repo_git(state, &["cat-file", "-t", &expr])
                .map(|o| String::from_utf8_lossy(&o).trim() == "tree")
                .unwrap_or(false);
            if !is_tree {
                respond_error(req, 404, "not a directory at that ref");
                return;
            }
            let Ok(out) = repo_git(state, &["ls-tree", "-z", "-l", &expr]) else {
                respond_error(req, 500, "ls-tree failed");
                return;
            };
            let mut entries = Vec::new();
            for line in String::from_utf8_lossy(&out).split('\0') {
                if line.is_empty() {
                    continue;
                }
                let (meta, name) = line.split_once('\t').unwrap_or((line, ""));
                let fields: Vec<&str> = meta.split_whitespace().collect();
                let [mode, kind, oid, size] = fields.as_slice() else {
                    continue;
                };
                let mut entry = serde_json::json!({
                    // git-server serves modes as stored in tree objects
                    // (no leading zero on trees: "40000").
                    "mode": mode.trim_start_matches('0'),
                    "kind": if *kind == "tree" { "tree" } else { "blob" },
                    "oid": oid,
                    "name": name,
                });
                if let Ok(n) = size.parse::<u64>() {
                    entry["size"] = serde_json::json!(n);
                }
                entries.push(entry);
            }
            let body =
                serde_json::json!({ "commit": commit, "path": path, "entries": entries });
            json_response(req, body.to_string());
        }
        [_repo, "file", refish, path @ ..] => {
            bump(state, CAT_API_FILE);
            let path = path.join("/");
            let Some(commit) = resolve_refish(state, refish) else {
                respond_error(req, 404, &format!("unknown ref {refish}"));
                return;
            };
            let expr = format!("{commit}:{path}");
            let is_blob = repo_git(state, &["cat-file", "-t", &expr])
                .map(|o| String::from_utf8_lossy(&o).trim() == "blob")
                .unwrap_or(false);
            if !is_blob {
                respond_error(req, 404, "no such file at that ref");
                return;
            }
            match repo_git(state, &["cat-file", "blob", &expr]) {
                Ok(data) => {
                    let _ = req.respond(
                        tiny_http::Response::from_data(data).with_header(
                            tiny_http::Header::from_bytes(
                                &b"Content-Type"[..],
                                &b"application/octet-stream"[..],
                            )
                            .unwrap(),
                        ),
                    );
                }
                Err(_) => respond_error(req, 500, "cat-file failed"),
            }
        }
        _ => respond_error(req, 404, "not found"),
    }
}

/// Serve a smart-HTTP request through the `git http-backend` CGI.
fn handle_smart(state: &ServerState, mut req: tiny_http::Request, path: &str, query: &str) {
    let mut body = Vec::new();
    if req.as_reader().read_to_end(&mut body).is_err() {
        respond_error(req, 400, "bad body");
        return;
    }
    let method = req.method().as_str().to_string();
    let mut cmd = Command::new("git");
    cmd.arg("http-backend")
        // The bare repo is <parent>/repo, so PATH_INFO's leading /repo
        // resolves to it under GIT_PROJECT_ROOT=<parent>.
        .env("GIT_PROJECT_ROOT", state.bare.parent().unwrap())
        .env("GIT_HTTP_EXPORT_ALL", "1")
        .env("REQUEST_METHOD", &method)
        .env("PATH_INFO", path)
        .env("QUERY_STRING", query)
        .env("REMOTE_ADDR", "127.0.0.1")
        .env("CONTENT_LENGTH", body.len().to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null());
    for header in req.headers() {
        let field = header.field.as_str().as_str();
        let value = header.value.as_str();
        match field.to_ascii_lowercase().as_str() {
            "content-type" => {
                cmd.env("CONTENT_TYPE", value);
            }
            // CGI convention: other headers become HTTP_*; http-backend
            // reads HTTP_GIT_PROTOCOL (protocol v2) and
            // HTTP_CONTENT_ENCODING (gzipped request bodies) from these.
            other => {
                let key = format!("HTTP_{}", other.to_ascii_uppercase().replace('-', "_"));
                cmd.env(key, value);
            }
        }
    }
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            respond_error(req, 500, &format!("spawn http-backend: {e}"));
            return;
        }
    };
    {
        use std::io::Write;
        let mut stdin = child.stdin.take().unwrap();
        let _ = stdin.write_all(&body);
    }
    let out = match child.wait_with_output() {
        Ok(o) => o,
        Err(e) => {
            respond_error(req, 500, &format!("http-backend: {e}"));
            return;
        }
    };
    // Parse the CGI response: headers, blank line, body.
    let split = out
        .stdout
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|i| (i, i + 4))
        .or_else(|| {
            out.stdout
                .windows(2)
                .position(|w| w == b"\n\n")
                .map(|i| (i, i + 2))
        });
    let Some((header_end, body_start)) = split else {
        respond_error(req, 500, "bad CGI response");
        return;
    };
    let header_text = String::from_utf8_lossy(&out.stdout[..header_end]).into_owned();
    let mut status = 200u16;
    let mut headers = Vec::new();
    for line in header_text.lines() {
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        let value = value.trim();
        if name.eq_ignore_ascii_case("Status") {
            status = value
                .split(' ')
                .next()
                .and_then(|s| s.parse().ok())
                .unwrap_or(200);
        } else if let Ok(h) = tiny_http::Header::from_bytes(name.as_bytes(), value.as_bytes()) {
            headers.push(h);
        }
    }
    let mut resp = tiny_http::Response::from_data(out.stdout[body_start..].to_vec())
        .with_status_code(status);
    for h in headers {
        resp = resp.with_header(h);
    }
    let _ = req.respond(resp);
}
