//! A local proxy that records the HTTP requests a command makes. HTTPS goes
//! through a certificate authority created for one run, which only the
//! wrapped command trusts, through its environment.

use super::client::{self, hop_by_hop, split_host_port, Url};
use super::wire::{self, Framing, Head};
use super::{head_digest, Exchange};
use base64::Engine;
use rcgen::{
    BasicConstraints, CertificateParams, DnType, ExtendedKeyUsagePurpose, IsCa, KeyPair,
    KeyUsagePurpose,
};
use rustls::pki_types::{PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{ClientConfig, ServerConfig, ServerConnection, StreamOwned};
use std::collections::{BTreeSet, HashMap};
use std::fs::{self, OpenOptions};
use std::io::{self, BufRead, BufReader, Read, Write};
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::Duration;

#[derive(Debug, Default)]
pub struct Records {
    pub exchanges: Vec<Exchange>,
    /// Requests that memo can't check later, such as POSTs and tunnels it
    /// couldn't decrypt.
    pub opaque: BTreeSet<String>,
}

struct State {
    ca_cert: rcgen::Certificate,
    ca_key: KeyPair,
    /// The `Proxy-Authorization` value that clients must send.
    auth: String,
    upstream: Arc<ClientConfig>,
    leaves: Mutex<HashMap<String, Arc<ServerConfig>>>,
    records: Mutex<Records>,
}

pub struct Proxy {
    addr: SocketAddr,
    url: String,
    dir: PathBuf,
    state: Arc<State>,
    stop: Arc<AtomicBool>,
    accept: Option<JoinHandle<()>>,
}

fn other(e: impl std::fmt::Display) -> io::Error {
    io::Error::other(e.to_string())
}

fn write_private(path: &Path, data: &[u8]) -> io::Result<()> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)?
        .write_all(data)
}

fn pem(der: &[u8]) -> String {
    let b64 = base64::engine::general_purpose::STANDARD.encode(der);
    let mut out = String::from("-----BEGIN CERTIFICATE-----\n");
    for line in b64.as_bytes().chunks(64) {
        out.push_str(std::str::from_utf8(line).expect("base64 is ASCII"));
        out.push('\n');
    }
    out.push_str("-----END CERTIFICATE-----\n");
    out
}

fn random_hex(bytes: usize) -> io::Result<String> {
    let mut buf = vec![0u8; bytes];
    // SAFETY: getrandom writes at most buf.len() bytes into buf.
    let n = unsafe { libc::getrandom(buf.as_mut_ptr().cast(), buf.len(), 0) };
    if n != bytes as isize {
        return Err(io::Error::last_os_error());
    }
    Ok(buf.iter().map(|b| format!("{b:02x}")).collect())
}

impl Proxy {
    /// Starts a proxy on a loopback port and writes its certificate files
    /// to `dir`, a private directory that [`Proxy::finish`] deletes.
    pub fn start(dir: PathBuf) -> io::Result<Proxy> {
        let ca_key = KeyPair::generate().map_err(other)?;
        let mut params = CertificateParams::new(Vec::<String>::new()).map_err(other)?;
        params
            .distinguished_name
            .push(DnType::CommonName, "memo recording proxy (one run)");
        params.is_ca = IsCa::Ca(BasicConstraints::Constrained(0));
        params.key_usages = vec![KeyUsagePurpose::KeyCertSign, KeyUsagePurpose::CrlSign];
        let ca_cert = params.self_signed(&ca_key).map_err(other)?;

        let mut bundle = String::new();
        for cert in rustls_native_certs::load_native_certs().certs {
            bundle.push_str(&pem(&cert));
        }
        bundle.push_str(&ca_cert.pem());
        write_private(&dir.join("ca.pem"), ca_cert.pem().as_bytes())?;
        write_private(&dir.join("bundle.pem"), bundle.as_bytes())?;

        let token = random_hex(16)?;
        let auth = format!(
            "Basic {}",
            base64::engine::general_purpose::STANDARD.encode(format!("memo:{token}"))
        );
        let listener = TcpListener::bind("127.0.0.1:0")?;
        let addr = listener.local_addr()?;
        let state = Arc::new(State {
            ca_cert,
            ca_key,
            auth,
            upstream: client::tls_config()?,
            leaves: Mutex::new(HashMap::new()),
            records: Mutex::new(Records::default()),
        });
        let stop = Arc::new(AtomicBool::new(false));
        let accept = {
            let (state, stop) = (state.clone(), stop.clone());
            std::thread::spawn(move || {
                for conn in listener.incoming() {
                    if stop.load(Ordering::SeqCst) {
                        break;
                    }
                    if let Ok(conn) = conn {
                        let state = state.clone();
                        std::thread::spawn(move || {
                            let _ = handle(&state, conn);
                        });
                    }
                }
            })
        };
        Ok(Proxy {
            addr,
            url: format!("http://memo:{token}@{addr}"),
            dir,
            state,
            stop,
            accept: Some(accept),
        })
    }

    pub fn addr(&self) -> SocketAddr {
        self.addr
    }

    /// Returns the environment that sends a command's HTTP clients through
    /// the proxy and makes them trust its certificate authority.
    pub fn env(&self) -> Vec<(String, String)> {
        let bundle = self.dir.join("bundle.pem").display().to_string();
        let mut env: Vec<(String, String)> =
            ["http_proxy", "HTTP_PROXY", "https_proxy", "HTTPS_PROXY"]
                .iter()
                .map(|k| (k.to_string(), self.url.clone()))
                .collect();
        for k in [
            "SSL_CERT_FILE",
            "CURL_CA_BUNDLE",
            "REQUESTS_CA_BUNDLE",
            "GIT_SSL_CAINFO",
            "CARGO_HTTP_CAINFO",
            "PIP_CERT",
            "AWS_CA_BUNDLE",
        ] {
            env.push((k.to_string(), bundle.clone()));
        }
        env.push((
            "NODE_EXTRA_CA_CERTS".into(),
            self.dir.join("ca.pem").display().to_string(),
        ));
        env.push(("NODE_USE_ENV_PROXY".into(), "1".into()));
        env
    }

    /// Stops accepting connections, deletes the certificate files, and
    /// returns what the proxy recorded.
    pub fn finish(mut self) -> Records {
        self.stop.store(true, Ordering::SeqCst);
        let _ = TcpStream::connect(self.addr);
        if let Some(t) = self.accept.take() {
            let _ = t.join();
        }
        let _ = fs::remove_dir_all(&self.dir);
        let mut records = self.state.records.lock().unwrap_or_else(|e| e.into_inner());
        std::mem::take(&mut *records)
    }
}

impl State {
    fn opaque(&self, what: String) {
        self.records
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .opaque
            .insert(what);
    }

    /// Returns a TLS server configuration with a certificate for `host`
    /// signed by the run's certificate authority.
    fn server_config(&self, host: &str) -> io::Result<Arc<ServerConfig>> {
        let mut leaves = self.leaves.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(c) = leaves.get(host) {
            return Ok(c.clone());
        }
        let key = KeyPair::generate().map_err(other)?;
        let mut params = CertificateParams::new(vec![host.to_string()]).map_err(other)?;
        params.distinguished_name.push(DnType::CommonName, host);
        params.extended_key_usages = vec![ExtendedKeyUsagePurpose::ServerAuth];
        let cert = params
            .signed_by(&key, &self.ca_cert, &self.ca_key)
            .map_err(other)?;
        let chain = vec![cert.der().clone(), self.ca_cert.der().clone()];
        let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key.serialize_der()));
        let provider = Arc::new(rustls::crypto::ring::default_provider());
        let mut config = ServerConfig::builder_with_provider(provider)
            .with_safe_default_protocol_versions()
            .map_err(other)?
            .with_no_client_auth()
            .with_single_cert(chain, key)
            .map_err(other)?;
        config.alpn_protocols = vec![b"http/1.1".to_vec()];
        let config = Arc::new(config);
        leaves.insert(host.to_string(), config.clone());
        Ok(config)
    }

    fn record(
        &self,
        method: &str,
        url: &str,
        headers: Vec<(String, String)>,
        resp: &Head,
        status: u16,
        body: String,
    ) {
        let mut records = self.records.lock().unwrap_or_else(|e| e.into_inner());
        if method != "GET" && method != "HEAD" {
            records.opaque.insert(format!("sent {method} {url}"));
            return;
        }
        let ex = Exchange {
            method: method.to_string(),
            url: url.to_string(),
            headers,
            status,
            etag: resp.get("etag").map(str::to_string),
            last_modified: resp.get("last-modified").map(str::to_string),
            body: if method == "HEAD" {
                head_digest(resp, status)
            } else {
                body
            },
        };
        let same_request =
            |e: &&Exchange| e.method == ex.method && e.url == ex.url && e.headers == ex.headers;
        if let Some(prev) = records.exchanges.iter().find(same_request) {
            if prev.status != ex.status || prev.body != ex.body {
                records.opaque.insert(format!(
                    "{method} {url} returned different responses during the run"
                ));
            }
            return;
        }
        records.exchanges.push(ex);
    }
}

fn respond(w: &mut impl Write, status: &str, msg: &str) -> io::Result<()> {
    write!(
        w,
        "HTTP/1.1 {status}\r\nContent-Type: text/plain\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{msg}",
        msg.len()
    )?;
    w.flush()
}

fn handle(state: &State, mut client: TcpStream) -> io::Result<()> {
    client.set_read_timeout(Some(Duration::from_secs(60)))?;
    let Some(head) = wire::read_head_exact(&mut client)? else {
        return Ok(());
    };
    if head.get("proxy-authorization") != Some(state.auth.as_str()) {
        return client.write_all(
            b"HTTP/1.1 407 Proxy Authentication Required\r\nProxy-Authenticate: Basic realm=\"memo\"\r\nContent-Length: 0\r\nConnection: close\r\n\r\n",
        );
    }
    let (method, target) = head.request()?;
    if !method.eq_ignore_ascii_case("CONNECT") {
        let mut r = BufReader::new(client);
        return serve(state, &head, &mut r, "");
    }
    let target = target.to_string();
    let (host, port) = split_host_port(&target, 443)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "bad CONNECT target"))?;
    client.write_all(b"HTTP/1.1 200 Connection Established\r\n\r\n")?;
    let mut first = [0u8; 1];
    if client.peek(&mut first)? == 0 {
        return Ok(());
    }
    if first[0] != 0x16 {
        state.opaque(format!("opened a tunnel to {target} that wasn't TLS"));
        return tunnel(client, &host, port);
    }
    let config = state.server_config(&host)?;
    let conn = ServerConnection::new(config).map_err(other)?;
    let mut tls = BufReader::new(StreamOwned::new(conn, client));
    let Some(req) = wire::read_head(&mut tls)? else {
        return Ok(());
    };
    let origin = Url {
        https: true,
        host,
        port,
        path: "/".into(),
    }
    .origin();
    serve(state, &req, &mut tls, &origin)?;
    let s = tls.get_mut();
    s.conn.send_close_notify();
    s.flush()
}

/// Forwards one request and its response, then records the exchange.
fn serve<S: Read + Write>(
    state: &State,
    head: &Head,
    r: &mut BufReader<S>,
    origin: &str,
) -> io::Result<()> {
    let (method, target) = head.request()?;
    let full = if target.starts_with("http://") || target.starts_with("https://") {
        target.to_string()
    } else {
        format!("{origin}{target}")
    };
    let url = match Url::parse(&full) {
        Ok(u) => u,
        Err(e) => return respond(r.get_mut(), "400 Bad Request", &e.to_string()),
    };
    if head
        .get("expect")
        .is_some_and(|e| e.eq_ignore_ascii_case("100-continue"))
    {
        r.get_mut().write_all(b"HTTP/1.1 100 Continue\r\n\r\n")?;
    }
    let framing = wire::request_framing(head)?;
    let headers: Vec<(String, String)> = head
        .headers
        .iter()
        .filter(|(k, _)| !hop_by_hop(k))
        .cloned()
        .collect();
    let body = (framing != Framing::Empty).then_some((&mut *r as &mut dyn BufRead, framing));
    let mut resp = match client::send(&state.upstream, method, &url, &headers, body) {
        Ok(resp) => resp,
        Err(e) => {
            state.opaque(format!("{method} {full} failed: {e}"));
            return respond(r.get_mut(), "502 Bad Gateway", &format!("memo: {e}"));
        }
    };
    let mut out = Head {
        line: resp.head.line.clone(),
        headers: resp
            .head
            .headers
            .iter()
            .filter(|(k, _)| {
                !["connection", "keep-alive", "proxy-connection"]
                    .iter()
                    .any(|h| k.eq_ignore_ascii_case(h))
            })
            .cloned()
            .collect(),
    };
    out.headers.push(("Connection".into(), "close".into()));
    let w = r.get_mut();
    w.write_all(&out.encode())?;
    let framing = wire::response_framing(method, resp.status, &resp.head)?;
    let hash = wire::copy_body(&mut resp.body, w, framing)?;
    w.flush()?;
    state.record(method, &full, headers, &resp.head, resp.status, hash);
    Ok(())
}

/// Copies bytes both ways between the client and `host:port`.
fn tunnel(client: TcpStream, host: &str, port: u16) -> io::Result<()> {
    let upstream = TcpStream::connect((host, port))?;
    let (mut c_read, mut u_write) = (client.try_clone()?, upstream.try_clone()?);
    let up = std::thread::spawn(move || {
        let _ = io::copy(&mut c_read, &mut u_write);
        let _ = u_write.shutdown(Shutdown::Write);
    });
    let (mut u_read, mut c_write) = (upstream, client);
    let _ = io::copy(&mut u_read, &mut c_write);
    let _ = c_write.shutdown(Shutdown::Write);
    let _ = up.join();
    Ok(())
}
