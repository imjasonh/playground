//! End-to-end tests for `--http`: curl fetches from a local server through
//! memo's recording proxy.

use rcgen::{BasicConstraints, CertificateParams, IsCa, KeyPair};
use rustls::pki_types::{PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{ServerConfig, ServerConnection, StreamOwned};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener};
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::{Arc, Mutex};

/// How the test server deviates from a well-behaved origin.
#[derive(Clone, Copy, Default)]
struct Quirks {
    weak_etag: bool,
    no_validators: bool,
    refuse_head: bool,
    ignore_conditionals: bool,
}

#[derive(Default)]
struct Log {
    body: String,
    /// The method and status of every request, in order.
    seen: Vec<(String, u16)>,
}

/// An HTTP server whose body can change. It sends an ETag and answers a
/// matching If-None-Match with 304, unless its quirks say otherwise.
struct Server {
    addr: SocketAddr,
    log: Arc<Mutex<Log>>,
}

impl Server {
    fn start(body: &str, quirks: Quirks, tls: Option<Arc<ServerConfig>>) -> Server {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let log = Arc::new(Mutex::new(Log {
            body: body.to_string(),
            seen: vec![],
        }));
        let shared = log.clone();
        std::thread::spawn(move || {
            for conn in listener.incoming().flatten() {
                let (log, tls) = (shared.clone(), tls.clone());
                std::thread::spawn(move || match tls {
                    Some(cfg) => {
                        let mut s = StreamOwned::new(ServerConnection::new(cfg).unwrap(), conn);
                        answer(&mut s, &log, quirks);
                        s.conn.send_close_notify();
                        let _ = s.flush();
                    }
                    None => answer(&mut { conn }, &log, quirks),
                });
            }
        });
        Server { addr, log }
    }

    fn plain(body: &str, quirks: Quirks) -> Server {
        Server::start(body, quirks, None)
    }

    fn set_body(&self, body: &str) {
        self.log.lock().unwrap().body = body.to_string();
    }

    fn seen(&self) -> Vec<(String, u16)> {
        self.log.lock().unwrap().seen.clone()
    }

    fn clear(&self) {
        self.log.lock().unwrap().seen.clear();
    }
}

fn answer(s: &mut impl ReadWrite, log: &Mutex<Log>, quirks: Quirks) {
    let mut head = Vec::new();
    let mut byte = [0u8; 1];
    while !head.ends_with(b"\r\n\r\n") {
        if s.read(&mut byte).unwrap_or(0) == 0 {
            return;
        }
        head.push(byte[0]);
    }
    let head = String::from_utf8_lossy(&head).into_owned();
    let method = head.split(' ').next().unwrap_or_default().to_string();
    let lower = head.to_ascii_lowercase();
    if let Some(len) = lower
        .lines()
        .find_map(|l| l.strip_prefix("content-length:"))
        .and_then(|v| v.trim().parse::<usize>().ok())
    {
        let mut body = vec![0u8; len];
        let _ = s.read_exact(&mut body);
    }
    let mut log = log.lock().unwrap();
    let tag = &blake3::hash(log.body.as_bytes()).to_hex()[..16];
    let etag = format!("{}\"{tag}\"", if quirks.weak_etag { "W/" } else { "" });
    let validators = if quirks.no_validators {
        String::new()
    } else {
        format!("ETag: {etag}\r\n")
    };
    let matched = !quirks.ignore_conditionals
        && !quirks.no_validators
        && lower.lines().any(|l| {
            l.strip_prefix("if-none-match:")
                .is_some_and(|v| v.trim().trim_start_matches("w/") == format!("\"{tag}\""))
        });
    let (status, reply) = if method == "HEAD" && quirks.refuse_head {
        (
            405,
            "HTTP/1.1 405 Method Not Allowed\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
                .to_string(),
        )
    } else if matched {
        (
            304,
            format!("HTTP/1.1 304 Not Modified\r\n{validators}Connection: close\r\n\r\n"),
        )
    } else {
        let body = if method == "HEAD" {
            ""
        } else {
            log.body.as_str()
        };
        (
            200,
            format!(
                "HTTP/1.1 200 OK\r\n{validators}Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
                log.body.len()
            ),
        )
    };
    log.seen.push((method, status));
    let _ = s.write_all(reply.as_bytes());
}

trait ReadWrite: Read + Write {}
impl<T: Read + Write> ReadWrite for T {}

fn have_curl() -> bool {
    Command::new("curl").arg("--version").output().is_ok()
}

struct Memo {
    dir: tempfile::TempDir,
    env: Vec<(String, String)>,
}

impl Memo {
    fn new() -> Memo {
        Memo {
            dir: tempfile::tempdir().unwrap(),
            env: vec![],
        }
    }

    fn run(&self, args: &[&str]) -> Output {
        let mut c = Command::new(env!("CARGO_BIN_EXE_memo"));
        c.arg("-v")
            .args(args)
            .env("MEMO_CACHE_DIR", self.dir.path().join("cache"))
            .current_dir(self.dir.path())
            .stdin(Stdio::null());
        for k in [
            "NO_PROXY",
            "no_proxy",
            "HTTP_PROXY",
            "http_proxy",
            "HTTPS_PROXY",
            "https_proxy",
            "ALL_PROXY",
            "all_proxy",
        ] {
            c.env_remove(k);
        }
        c.envs(self.env.iter().map(|(k, v)| (k, v)));
        c.output().unwrap()
    }

    /// Runs `memo --http curl -sS URL`.
    fn fetch(&self, url: &str) -> Fetch {
        Fetch(self.run(&["--http", "curl", "-sS", url]))
    }
}

struct Fetch(Output);

impl Fetch {
    fn stdout(&self) -> String {
        String::from_utf8_lossy(&self.0.stdout).into_owned()
    }

    fn stderr(&self) -> String {
        String::from_utf8_lossy(&self.0.stderr).into_owned()
    }

    #[track_caller]
    fn replayed(&self) -> &Fetch {
        assert!(
            self.stderr().contains("memo: replaying"),
            "{}",
            self.stderr()
        );
        self
    }

    #[track_caller]
    fn reran(&self, why: &str) -> &Fetch {
        let err = self.stderr();
        assert!(
            err.contains("memo: running") && err.contains(why),
            "expected a rerun because of {why:?}:\n{err}"
        );
        self
    }
}

fn seen(list: &[(&str, u16)]) -> Vec<(String, u16)> {
    list.iter().map(|(m, s)| (m.to_string(), *s)).collect()
}

/// Records a fetch of `server`, then clears its log so the test sees only
/// the requests that later calls make.
fn recorded(server: &Server, memo: &Memo, url: &str) {
    let first = memo.fetch(url);
    assert!(
        first.stderr().contains("1 HTTP requests"),
        "{}",
        first.stderr()
    );
    assert_eq!(server.seen(), seen(&[("GET", 200)]));
    server.clear();
}

#[test]
fn a_head_request_confirms_an_unchanged_resource() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let server = Server::plain("one", Quirks::default());
    let memo = Memo::new();
    let url = format!("http://{}/data", server.addr);
    recorded(&server, &memo, &url);
    assert_eq!(memo.fetch(&url).replayed().stdout(), "one");
    assert_eq!(server.seen(), seen(&[("HEAD", 304)]));
}

#[test]
fn a_changed_resource_is_found_without_downloading_it_twice() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let server = Server::plain("one", Quirks::default());
    let memo = Memo::new();
    let url = format!("http://{}/data", server.addr);
    recorded(&server, &memo, &url);
    server.set_body("two");
    let rerun = memo.fetch(&url);
    rerun.reran("ETag changed");
    assert_eq!(rerun.stdout(), "two");
    // The check costs one bodyless HEAD; only the rerun downloads.
    assert_eq!(server.seen(), seen(&[("HEAD", 200), ("GET", 200)]));
}

#[test]
fn weak_entity_tags_still_match() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let quirks = Quirks {
        weak_etag: true,
        ..Quirks::default()
    };
    let server = Server::plain("one", quirks);
    let memo = Memo::new();
    let url = format!("http://{}/data", server.addr);
    recorded(&server, &memo, &url);
    memo.fetch(&url).replayed();
    assert_eq!(server.seen(), seen(&[("HEAD", 304)]));
}

#[test]
fn memo_compares_tags_itself_when_the_server_ignores_conditions() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let quirks = Quirks {
        ignore_conditionals: true,
        ..Quirks::default()
    };
    let server = Server::plain("one", quirks);
    let memo = Memo::new();
    let url = format!("http://{}/data", server.addr);
    recorded(&server, &memo, &url);
    memo.fetch(&url).replayed();
    assert_eq!(server.seen(), seen(&[("HEAD", 200)]));
    server.set_body("two");
    memo.fetch(&url).reran("ETag changed");
}

#[test]
fn a_refused_head_falls_back_to_get() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let quirks = Quirks {
        refuse_head: true,
        ..Quirks::default()
    };
    let server = Server::plain("one", quirks);
    let memo = Memo::new();
    let url = format!("http://{}/data", server.addr);
    recorded(&server, &memo, &url);
    memo.fetch(&url).replayed();
    assert_eq!(server.seen(), seen(&[("HEAD", 405), ("GET", 304)]));
}

#[test]
fn without_validators_the_response_is_hashed() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let quirks = Quirks {
        no_validators: true,
        ..Quirks::default()
    };
    let server = Server::plain("one", quirks);
    let memo = Memo::new();
    let url = format!("http://{}/data", server.addr);
    recorded(&server, &memo, &url);
    memo.fetch(&url).replayed();
    assert_eq!(server.seen(), seen(&[("GET", 200)]));
    server.set_body("two");
    assert_eq!(memo.fetch(&url).reran("response changed").stdout(), "two");
}

#[test]
fn other_methods_need_a_ttl() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let server = Server::plain("ok", Quirks::default());
    let memo = Memo::new();
    let url = format!("http://{}/submit", server.addr);
    let post = Fetch(memo.run(&["--http", "curl", "-sS", "-d", "x=1", url.as_str()]));
    assert_eq!(post.stdout(), "ok", "{}", post.stderr());
    assert!(
        post.stderr().contains(&format!("sent POST {url}")),
        "{}",
        post.stderr()
    );
    let ttl = Fetch(memo.run(&[
        "--http",
        "--ttl",
        "1h",
        "curl",
        "-sS",
        "-d",
        "x=1",
        url.as_str(),
    ]));
    assert!(
        ttl.stderr().contains("memo: cached the result"),
        "{}",
        ttl.stderr()
    );
}

#[test]
fn the_proxy_rejects_clients_without_its_password() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let server = Server::plain("secret", Quirks::default());
    let memo = Memo::new();
    let script = format!(
        "curl -s -o /dev/null -w '%{{http_code}}' -x \"http://${{http_proxy##*@}}\" http://{}/",
        server.addr
    );
    let out = Fetch(memo.run(&["--http", "sh", "-c", &script]));
    assert_eq!(out.stdout(), "407", "{}", out.stderr());
}

#[test]
fn https_is_intercepted_and_verified() {
    if !have_curl() {
        return eprintln!("skipping: curl isn't installed");
    }
    let ca_key = KeyPair::generate().unwrap();
    let mut ca = CertificateParams::new(Vec::<String>::new()).unwrap();
    ca.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
    let ca = ca.self_signed(&ca_key).unwrap();
    let leaf_key = KeyPair::generate().unwrap();
    let leaf = CertificateParams::new(vec!["127.0.0.1".to_string()])
        .unwrap()
        .signed_by(&leaf_key, &ca, &ca_key)
        .unwrap();
    let provider = Arc::new(rustls::crypto::ring::default_provider());
    let config = ServerConfig::builder_with_provider(provider)
        .with_safe_default_protocol_versions()
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(
            vec![leaf.der().clone(), ca.der().clone()],
            PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(leaf_key.serialize_der())),
        )
        .unwrap();
    let server = Server::start("over tls", Quirks::default(), Some(Arc::new(config)));

    let mut memo = Memo::new();
    let ca_file: PathBuf = memo.dir.path().join("test-ca.pem");
    std::fs::write(&ca_file, ca.pem()).unwrap();
    // memo verifies the origin against SSL_CERT_FILE; the command gets a
    // bundle of those roots plus memo's own authority.
    memo.env
        .push(("SSL_CERT_FILE".into(), ca_file.display().to_string()));
    let url = format!("https://127.0.0.1:{}/doc", server.addr.port());
    let first = memo.fetch(&url);
    assert_eq!(first.stdout(), "over tls", "{}", first.stderr());
    memo.fetch(&url).replayed();
    assert_eq!(server.seen(), seen(&[("GET", 200), ("HEAD", 304)]));
}
