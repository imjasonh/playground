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

#[derive(Default)]
struct Log {
    body: String,
    /// Status codes the server sent, in order.
    sent: Vec<u16>,
}

/// An HTTP server whose body can change. It sends an ETag and answers a
/// matching If-None-Match with 304.
struct Server {
    addr: SocketAddr,
    log: Arc<Mutex<Log>>,
}

impl Server {
    fn start(body: &str, tls: Option<Arc<ServerConfig>>) -> Server {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let log = Arc::new(Mutex::new(Log {
            body: body.to_string(),
            sent: vec![],
        }));
        let shared = log.clone();
        std::thread::spawn(move || {
            for conn in listener.incoming().flatten() {
                let (log, tls) = (shared.clone(), tls.clone());
                std::thread::spawn(move || match tls {
                    Some(cfg) => {
                        let mut s = StreamOwned::new(ServerConnection::new(cfg).unwrap(), conn);
                        answer(&mut s, &log);
                        s.conn.send_close_notify();
                        let _ = s.flush();
                    }
                    None => answer(&mut { conn }, &log),
                });
            }
        });
        Server { addr, log }
    }

    fn set_body(&self, body: &str) {
        self.log.lock().unwrap().body = body.to_string();
    }

    fn sent(&self) -> Vec<u16> {
        self.log.lock().unwrap().sent.clone()
    }
}

fn answer(s: &mut impl ReadWrite, log: &Mutex<Log>) {
    let mut head = Vec::new();
    let mut byte = [0u8; 1];
    while !head.ends_with(b"\r\n\r\n") {
        if s.read(&mut byte).unwrap_or(0) == 0 {
            return;
        }
        head.push(byte[0]);
    }
    let head = String::from_utf8_lossy(&head).to_ascii_lowercase();
    if let Some(len) = head
        .lines()
        .find_map(|l| l.strip_prefix("content-length:"))
        .and_then(|v| v.trim().parse::<usize>().ok())
    {
        let mut body = vec![0u8; len];
        let _ = s.read_exact(&mut body);
    }
    let mut log = log.lock().unwrap();
    let etag = format!("\"{}\"", &blake3::hash(log.body.as_bytes()).to_hex()[..16]);
    let matched = head.lines().any(|l| {
        l.strip_prefix("if-none-match:")
            .is_some_and(|v| v.trim() == etag)
    });
    let reply = if matched {
        log.sent.push(304);
        format!("HTTP/1.1 304 Not Modified\r\nETag: {etag}\r\nConnection: close\r\n\r\n")
    } else {
        log.sent.push(200);
        format!(
            "HTTP/1.1 200 OK\r\nETag: {etag}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
            log.body.len(),
            log.body
        )
    };
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
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

#[test]
fn get_requests_are_checked_again_before_replay() {
    if !have_curl() {
        eprintln!("skipping: curl isn't installed");
        return;
    }
    let server = Server::start("one", None);
    let memo = Memo::new();
    let url = format!("http://{}/data", server.addr);
    let args = ["--http", "curl", "-sS", url.as_str()];

    let first = memo.run(&args);
    assert_eq!(stdout(&first), "one", "{}", stderr(&first));
    assert!(
        stderr(&first).contains("1 HTTP requests"),
        "{}",
        stderr(&first)
    );

    let second = memo.run(&args);
    assert!(
        stderr(&second).contains("memo: replaying"),
        "{}",
        stderr(&second)
    );
    assert_eq!(stdout(&second), "one");
    assert_eq!(
        server.sent(),
        vec![200, 304],
        "the replay should revalidate with If-None-Match"
    );

    server.set_body("two");
    let third = memo.run(&args);
    assert!(
        stderr(&third).contains("response changed"),
        "{}",
        stderr(&third)
    );
    assert_eq!(stdout(&third), "two");
}

#[test]
fn other_methods_need_a_ttl() {
    if !have_curl() {
        eprintln!("skipping: curl isn't installed");
        return;
    }
    let server = Server::start("ok", None);
    let memo = Memo::new();
    let url = format!("http://{}/submit", server.addr);
    let post = memo.run(&["--http", "curl", "-sS", "-d", "x=1", url.as_str()]);
    assert_eq!(stdout(&post), "ok", "{}", stderr(&post));
    assert!(
        stderr(&post).contains(&format!("sent POST {url}")),
        "{}",
        stderr(&post)
    );
    let ttl = memo.run(&[
        "--http",
        "--ttl",
        "1h",
        "curl",
        "-sS",
        "-d",
        "x=1",
        url.as_str(),
    ]);
    assert!(
        stderr(&ttl).contains("memo: cached the result"),
        "{}",
        stderr(&ttl)
    );
}

#[test]
fn the_proxy_rejects_clients_without_its_password() {
    if !have_curl() {
        eprintln!("skipping: curl isn't installed");
        return;
    }
    let server = Server::start("secret", None);
    let memo = Memo::new();
    let script = format!(
        "curl -s -o /dev/null -w '%{{http_code}}' -x \"http://${{http_proxy##*@}}\" http://{}/",
        server.addr
    );
    let out = memo.run(&["--http", "sh", "-c", &script]);
    assert_eq!(stdout(&out), "407", "{}", stderr(&out));
}

#[test]
fn https_is_intercepted_and_verified() {
    if !have_curl() {
        eprintln!("skipping: curl isn't installed");
        return;
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
    let server = Server::start("over tls", Some(Arc::new(config)));

    let mut memo = Memo::new();
    let ca_file: PathBuf = memo.dir.path().join("test-ca.pem");
    std::fs::write(&ca_file, ca.pem()).unwrap();
    // memo verifies the origin against SSL_CERT_FILE; the command gets a
    // bundle of those roots plus memo's own authority.
    memo.env
        .push(("SSL_CERT_FILE".into(), ca_file.display().to_string()));
    let url = format!("https://127.0.0.1:{}/doc", server.addr.port());
    let args = ["--http", "curl", "-sS", url.as_str()];

    let first = memo.run(&args);
    assert_eq!(stdout(&first), "over tls", "{}", stderr(&first));
    assert!(
        stderr(&first).contains("1 HTTP requests"),
        "{}",
        stderr(&first)
    );
    let second = memo.run(&args);
    assert!(
        stderr(&second).contains("memo: replaying"),
        "{}",
        stderr(&second)
    );
    assert_eq!(server.sent(), vec![200, 304]);
}
