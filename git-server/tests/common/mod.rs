//! Native test harness: serves [`git_server::http::GitHttp`] over real
//! localhost HTTP (tiny_http) so integration tests can drive it with an
//! actual `git` client — the same handler code that runs in the Worker, with
//! in-memory storage in place of R2/Durable Objects.

use git_server::http::{GitHttp, Request as GitRequest};
use git_server::protocol::BodyStream;
use git_server::refs::MemStateStore;
use git_server::storage::MemStore;
use std::io::Read;
use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// A running test server.
pub struct TestServer {
    pub store: MemStore,
    pub states: MemStateStore,
    pub port: u16,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
    handle: Option<std::thread::JoinHandle<()>>,
}

struct ReaderBody<R: Read> {
    reader: R,
    done: bool,
}

#[async_trait::async_trait(?Send)]
impl<R: Read> BodyStream for ReaderBody<R> {
    async fn next_chunk(&mut self) -> Result<Option<Vec<u8>>, String> {
        if self.done {
            return Ok(None);
        }
        let mut buf = vec![0u8; 64 * 1024];
        match self.reader.read(&mut buf) {
            Ok(0) => {
                self.done = true;
                Ok(None)
            }
            Ok(n) => {
                buf.truncate(n);
                Ok(Some(buf))
            }
            Err(e) => Err(e.to_string()),
        }
    }
}

static NONCE: AtomicU64 = AtomicU64::new(1);

impl TestServer {
    pub fn start() -> TestServer {
        Self::start_with_push_limit(git_server::http::DEFAULT_PUSH_LIMIT_BYTES)
    }

    /// Start with a custom per-push size limit (production default is
    /// Cloudflare's ~100 MB request-body cap; tests shrink it so the
    /// rejection path is exercised without moving 100 MB).
    pub fn start_with_push_limit(push_limit_bytes: u64) -> TestServer {
        let store = MemStore::new();
        let states = MemStateStore::new();
        let server = tiny_http::Server::http("127.0.0.1:0").expect("bind test server");
        let port = match server.server_addr() {
            tiny_http::ListenAddr::IP(addr) => addr.port(),
            _ => unreachable!(),
        };
        let shutdown = Arc::new(std::sync::atomic::AtomicBool::new(false));

        let store2 = store.clone();
        let states2 = states.clone();
        let shutdown2 = shutdown.clone();
        let handle = std::thread::spawn(move || loop {
            let request = match server.recv_timeout(std::time::Duration::from_millis(100)) {
                Ok(Some(r)) => r,
                Ok(None) => {
                    if shutdown2.load(Ordering::Relaxed) {
                        return;
                    }
                    continue;
                }
                Err(_) => return,
            };
            serve_one(&store2, &states2, push_limit_bytes, request);
        });

        TestServer {
            store,
            states,
            port,
            shutdown,
            handle: Some(handle),
        }
    }

    pub fn url(&self, repo: &str) -> String {
        format!("http://127.0.0.1:{}/{}", self.port, repo)
    }

    /// Simple blocking HTTP GET against the server (for the read APIs).
    pub fn get(&self, path: &str) -> (u16, Vec<u8>) {
        let (status, _, body) = self.request("GET", path);
        (status, body)
    }

    pub fn post(&self, path: &str) -> (u16, Vec<u8>) {
        let (status, _, body) = self.request("POST", path);
        (status, body)
    }

    /// GET returning (status, response header block, body) for tests that
    /// assert on headers (e.g. Server-Timing).
    pub fn get_with_headers(&self, path: &str) -> (u16, String, Vec<u8>) {
        self.request("GET", path)
    }

    fn request(&self, method: &str, path: &str) -> (u16, String, Vec<u8>) {
        use std::io::Write;
        let mut stream = std::net::TcpStream::connect(("127.0.0.1", self.port)).expect("connect");
        // HTTP/1.0 keeps the response un-chunked, so body extraction is a
        // simple split on the header terminator.
        write!(
            stream,
            "{method} {path} HTTP/1.0\r\nHost: localhost\r\nConnection: close\r\nContent-Length: 0\r\n\r\n"
        )
        .unwrap();
        let mut raw = Vec::new();
        stream.read_to_end(&mut raw).unwrap();
        let split = raw
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .expect("http response header");
        let head = String::from_utf8_lossy(&raw[..split]).to_string();
        let status: u16 = head
            .lines()
            .next()
            .and_then(|l| l.split_whitespace().nth(1))
            .and_then(|s| s.parse().ok())
            .expect("status line");
        (status, head, raw[split + 4..].to_vec())
    }
}

impl Drop for TestServer {
    fn drop(&mut self) {
        self.shutdown.store(true, Ordering::Relaxed);
        if let Some(h) = self.handle.take() {
            let _ = h.join();
        }
    }
}

fn serve_one(
    store: &MemStore,
    states: &MemStateStore,
    push_limit_bytes: u64,
    mut request: tiny_http::Request,
) {
    let method = request.method().as_str().to_string();
    let url = request.url().to_string();
    let (path, query) = match url.split_once('?') {
        Some((p, q)) => (p.to_string(), Some(q.to_string())),
        None => (url, None),
    };
    let header = |name: &str| -> Option<String> {
        request
            .headers()
            .iter()
            .find(|h| h.field.as_str().as_str().eq_ignore_ascii_case(name))
            .map(|h| h.value.as_str().to_string())
    };
    let git_protocol = header("Git-Protocol");
    let content_encoding = header("Content-Encoding");

    let server = GitHttp::new(
        std::rc::Rc::new(store.clone()),
        std::rc::Rc::new(states.clone()),
    )
    .with_push_limit(push_limit_bytes);
    let git_req = GitRequest {
        method: &method,
        path: &path,
        query: query.as_deref(),
        git_protocol: git_protocol.as_deref(),
        content_encoding: content_encoding.as_deref(),
    };
    let mut body = ReaderBody {
        reader: request.as_reader(),
        done: false,
    };
    let nonce = format!("t{}", NONCE.fetch_add(1, Ordering::Relaxed));
    let mut resp = futures::executor::block_on(server.handle(&git_req, &mut body, &nonce));
    let body_bytes = futures::executor::block_on(
        std::mem::replace(&mut resp.body, git_server::http::Body::Full(Vec::new())).into_bytes(),
    )
    .unwrap_or_else(|e| format!("stream error: {e}").into_bytes());

    let mut response = tiny_http::Response::from_data(body_bytes)
        .with_status_code(resp.status)
        .with_header(
            tiny_http::Header::from_bytes(&b"Content-Type"[..], resp.content_type.as_bytes())
                .unwrap(),
        );
    // Emit metrics exactly as the Worker does, so tests can assert on them
    // and the local benchmark scripts read the same header as remote ones.
    if let Some(header) = resp.server_timing() {
        response = response.with_header(
            tiny_http::Header::from_bytes(&b"Server-Timing"[..], header.as_bytes()).unwrap(),
        );
    }
    let _ = request.respond(response);
}

/// Run `git` with the given args in `dir`, panicking (with output) on failure.
pub fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_AUTHOR_NAME", "Test Author")
        .env("GIT_AUTHOR_EMAIL", "author@example.com")
        .env("GIT_COMMITTER_NAME", "Test Committer")
        .env("GIT_COMMITTER_EMAIL", "committer@example.com")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("HOME", dir) // isolate from any user gitconfig
        .output()
        .expect("run git");
    assert!(
        out.status.success(),
        "git {:?} failed:\nstdout: {}\nstderr: {}",
        args,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).to_string()
}

/// Like [`git`] but returns (success, combined output) instead of panicking.
pub fn git_try(dir: &Path, args: &[&str]) -> (bool, String) {
    let out = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_AUTHOR_NAME", "Test Author")
        .env("GIT_AUTHOR_EMAIL", "author@example.com")
        .env("GIT_COMMITTER_NAME", "Test Committer")
        .env("GIT_COMMITTER_EMAIL", "committer@example.com")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("HOME", dir)
        .output()
        .expect("run git");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), combined)
}

/// Write a file (creating parent dirs) inside a work tree.
pub fn write_file(dir: &Path, rel: &str, contents: &str) {
    let path = dir.join(rel);
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).unwrap();
    }
    std::fs::write(path, contents).unwrap();
}
