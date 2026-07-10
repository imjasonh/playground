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

use git_server_worker::http::{GitHttp, Request as GitRequest};
use git_server_worker::protocol::BodyStream;
use git_server_worker::refs::MemStateStore;
use git_server_worker::storage::MemStore;
use std::io::Read;
use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

// --- minimal copy of the test harness (benches can't import tests/) --------

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

fn start_server(store: MemStore, states: MemStateStore) -> (u16, std::thread::JoinHandle<()>) {
    let server = tiny_http::Server::http("127.0.0.1:0").expect("bind");
    let port = match server.server_addr() {
        tiny_http::ListenAddr::IP(addr) => addr.port(),
        _ => unreachable!(),
    };
    let handle = std::thread::spawn(move || {
        let mut nonce = 0u64;
        for mut request in server.incoming_requests() {
            nonce += 1;
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
            let git = GitHttp {
                store: &store,
                states: &states,
            };
            let req = GitRequest {
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
            let resp =
                futures::executor::block_on(git.handle(&req, &mut body, &format!("b{nonce}")));
            let response = tiny_http::Response::from_data(resp.body)
                .with_status_code(resp.status)
                .with_header(
                    tiny_http::Header::from_bytes(
                        &b"Content-Type"[..],
                        resp.content_type.as_bytes(),
                    )
                    .unwrap(),
                );
            let _ = request.respond(response);
        }
    });
    (port, handle)
}

fn git(dir: &Path, args: &[&str]) {
    let out = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_AUTHOR_NAME", "Bench")
        .env("GIT_AUTHOR_EMAIL", "bench@example.com")
        .env("GIT_COMMITTER_NAME", "Bench")
        .env("GIT_COMMITTER_EMAIL", "bench@example.com")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("HOME", dir) // isolate from any user gitconfig (proxies, rewrites)
        .output()
        .expect("run git");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

struct Phase {
    name: &'static str,
    wall: Duration,
    class_a: u64,
    class_b: u64,
}

fn main() {
    let commits = env_usize("LR_COMMITS", 200);
    let files = env_usize("LR_FILES", 2_000);
    let dirs = env_usize("LR_DIRS", 50);

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

    let store = MemStore::new();
    let states = MemStateStore::new();
    let (port, _server) = start_server(store.clone(), states.clone());
    let url = format!("http://127.0.0.1:{port}/bench");
    git(&src, &["remote", "add", "origin", &url]);

    let mut phases: Vec<Phase> = Vec::new();
    let mut run_phase = |name: &'static str, f: &mut dyn FnMut()| {
        store.reset_op_counts();
        let start = Instant::now();
        f();
        let ops = store.op_counts();
        phases.push(Phase {
            name,
            wall: start.elapsed(),
            class_a: ops.class_a,
            class_b: ops.class_b,
        });
    };

    // --- Phases -------------------------------------------------------------
    run_phase("push (full history)", &mut || {
        git(&src, &["push", "-q", "origin", "main"]);
    });

    let clone1 = tmp.path().join("clone1");
    run_phase("clone (full)", &mut || {
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
    run_phase("push (incremental, 5 commits)", &mut || {
        git(&src, &["push", "-q", "origin", "main"]);
    });
    run_phase("pull (incremental)", &mut || {
        git(&clone1, &["pull", "-q", "origin", "main"]);
    });

    // Read APIs straight through the router (no HTTP client noise).
    let api = |path: String| {
        let git = GitHttp {
            store: &store,
            states: &states,
        };
        let req = GitRequest {
            method: "GET",
            path: &path,
            query: None,
            git_protocol: None,
            content_encoding: None,
        };
        let mut body = ReaderBody {
            reader: std::io::empty(),
            done: false,
        };
        let resp = futures::executor::block_on(git.handle(&req, &mut body, "api"));
        assert_eq!(
            resp.status,
            200,
            "{path}: {}",
            String::from_utf8_lossy(&resp.body)
        );
        resp.body.len()
    };
    run_phase("file API (1 file)", &mut || {
        api("/api/bench/file/main/dir00/file0.txt".to_string());
    });
    run_phase("tree API (1 dir)", &mut || {
        api("/api/bench/tree/main/dir00".to_string());
    });
    run_phase("blame API (hot file)", &mut || {
        api("/api/bench/blame/main/dir00/file0.txt".to_string());
    });

    run_phase("repack", &mut || {
        let git = GitHttp {
            store: &store,
            states: &states,
        };
        let req = GitRequest {
            method: "POST",
            path: "/api/bench/repack",
            query: None,
            git_protocol: None,
            content_encoding: None,
        };
        let mut body = ReaderBody {
            reader: std::io::empty(),
            done: false,
        };
        let resp = futures::executor::block_on(git.handle(&req, &mut body, "repack"));
        assert_eq!(resp.status, 200);
        assert!(String::from_utf8_lossy(&resp.body).contains("Repacked"));
    });

    let clone2 = tmp.path().join("clone2");
    run_phase("clone (after repack)", &mut || {
        git(tmp.path(), &["clone", "-q", &url, clone2.to_str().unwrap()]);
    });
    run_phase("blame API (after repack)", &mut || {
        api("/api/bench/blame/main/dir00/file0.txt".to_string());
    });

    // --- Report ---------------------------------------------------------------
    let stored: u64 = store
        .keys()
        .iter()
        .map(|k| {
            futures::executor::block_on(git_server_worker::storage::Store::size(&store, k))
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
        "{:<32} {:>12} {:>10} {:>10}",
        "phase", "wall", "R2 classA", "R2 classB"
    );
    for p in &phases {
        println!(
            "{:<32} {:>12.2?} {:>10} {:>10}",
            p.name, p.wall, p.class_a, p.class_b
        );
    }
}
