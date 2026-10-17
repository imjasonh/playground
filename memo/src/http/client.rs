//! Sends one request to an origin server over plain TCP or TLS.

use super::wire::{self, Framing, Head};
use rustls::pki_types::ServerName;
use rustls::{ClientConfig, ClientConnection, RootCertStore, StreamOwned};
use std::io::{self, BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::sync::Arc;
use std::time::Duration;

const TIMEOUT: Duration = Duration::from_secs(60);

/// Header fields that describe one connection, not the request.
const HOP_BY_HOP: &[&str] = &[
    "connection",
    "keep-alive",
    "proxy-authorization",
    "proxy-authenticate",
    "proxy-connection",
    "te",
    "trailer",
    "upgrade",
    "expect",
    "host",
];

pub fn hop_by_hop(name: &str) -> bool {
    HOP_BY_HOP.iter().any(|h| name.eq_ignore_ascii_case(h))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Url {
    pub https: bool,
    pub host: String,
    pub port: u16,
    /// The path and query, starting with `/`.
    pub path: String,
}

impl Url {
    pub fn parse(s: &str) -> io::Result<Url> {
        let bad = || {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("unsupported URL {s:?}"),
            )
        };
        let (https, rest) = if let Some(r) = s.strip_prefix("https://") {
            (true, r)
        } else if let Some(r) = s.strip_prefix("http://") {
            (false, r)
        } else {
            return Err(bad());
        };
        let split = rest.find(['/', '?']).unwrap_or(rest.len());
        let (authority, path) = rest.split_at(split);
        let path = if path.starts_with('?') {
            format!("/{path}")
        } else if path.is_empty() {
            "/".to_string()
        } else {
            path.to_string()
        };
        let default = if https { 443 } else { 80 };
        let (host, port) = split_host_port(authority, default).ok_or_else(bad)?;
        Ok(Url {
            https,
            host,
            port,
            path,
        })
    }

    /// Returns the `Host` header value.
    pub fn authority(&self) -> String {
        let host = if self.host.contains(':') {
            format!("[{}]", self.host)
        } else {
            self.host.clone()
        };
        let default = if self.https { 443 } else { 80 };
        if self.port == default {
            host
        } else {
            format!("{host}:{}", self.port)
        }
    }

    pub fn origin(&self) -> String {
        format!(
            "{}://{}",
            if self.https { "https" } else { "http" },
            self.authority()
        )
    }
}

/// Splits `host:port`, `[v6]:port`, or a bare host.
pub fn split_host_port(s: &str, default: u16) -> Option<(String, u16)> {
    if let Some(rest) = s.strip_prefix('[') {
        let (host, after) = rest.split_once(']')?;
        let port = match after.strip_prefix(':') {
            Some(p) => p.parse().ok()?,
            None if after.is_empty() => default,
            None => return None,
        };
        return Some((host.to_string(), port));
    }
    match s.rsplit_once(':') {
        Some((h, p)) if !h.contains(':') => Some((h.to_string(), p.parse().ok()?)),
        _ if !s.is_empty() && !s.contains(':') => Some((s.to_string(), default)),
        _ => None,
    }
}

/// Returns a TLS client configuration that trusts the system's roots.
pub fn tls_config() -> io::Result<Arc<ClientConfig>> {
    let mut roots = RootCertStore::empty();
    for cert in rustls_native_certs::load_native_certs().certs {
        let _ = roots.add(cert);
    }
    let provider = Arc::new(rustls::crypto::ring::default_provider());
    let mut config = ClientConfig::builder_with_provider(provider)
        .with_safe_default_protocol_versions()
        .map_err(io::Error::other)?
        .with_root_certificates(roots)
        .with_no_client_auth();
    config.alpn_protocols = vec![b"http/1.1".to_vec()];
    Ok(Arc::new(config))
}

pub enum Conn {
    Plain(TcpStream),
    Tls(Box<StreamOwned<ClientConnection, TcpStream>>),
}

impl Read for Conn {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Conn::Plain(s) => s.read(buf),
            Conn::Tls(s) => match s.read(buf) {
                // Many servers close without a TLS close_notify; treat it as
                // the end of a close-delimited body.
                Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => Ok(0),
                other => other,
            },
        }
    }
}

impl Write for Conn {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Conn::Plain(s) => s.write(buf),
            Conn::Tls(s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Conn::Plain(s) => s.flush(),
            Conn::Tls(s) => s.flush(),
        }
    }
}

pub struct Response {
    pub status: u16,
    pub head: Head,
    pub body: BufReader<Conn>,
}

/// Sends `method url` with `headers` (minus hop-by-hop fields) and, if
/// given, a request body copied from `body` with its framing. Returns the
/// final response, skipping interim 1xx responses.
pub fn send(
    tls: &Arc<ClientConfig>,
    method: &str,
    url: &Url,
    headers: &[(String, String)],
    body: Option<(&mut dyn BufRead, Framing)>,
) -> io::Result<Response> {
    let tcp = TcpStream::connect((url.host.as_str(), url.port))?;
    tcp.set_read_timeout(Some(TIMEOUT))?;
    tcp.set_write_timeout(Some(TIMEOUT))?;
    let mut conn = if url.https {
        let name = ServerName::try_from(url.host.clone())
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e))?;
        let c = ClientConnection::new(tls.clone(), name).map_err(io::Error::other)?;
        Conn::Tls(Box::new(StreamOwned::new(c, tcp)))
    } else {
        Conn::Plain(tcp)
    };
    let mut head = Head {
        line: format!("{method} {} HTTP/1.1", url.path),
        headers: vec![("Host".into(), url.authority())],
    };
    head.headers
        .extend(headers.iter().filter(|(k, _)| !hop_by_hop(k)).cloned());
    head.headers.push(("Connection".into(), "close".into()));
    conn.write_all(&head.encode())?;
    if let Some((r, framing)) = body {
        wire::copy_body(r, &mut conn, framing)?;
    }
    conn.flush()?;
    let mut reader = BufReader::new(conn);
    loop {
        let head = wire::read_head(&mut reader)?.ok_or(io::ErrorKind::UnexpectedEof)?;
        let status = head.status()?;
        if (100..200).contains(&status) && status != 101 {
            continue;
        }
        return Ok(Response {
            status,
            head,
            body: reader,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn urls() {
        let u = Url::parse("https://example.com/a/b?c=1").unwrap();
        assert_eq!(
            (u.https, u.host.as_str(), u.port, u.path.as_str()),
            (true, "example.com", 443, "/a/b?c=1")
        );
        assert_eq!(u.authority(), "example.com");
        let u = Url::parse("http://127.0.0.1:8080").unwrap();
        assert_eq!(
            (u.port, u.path.as_str(), u.authority().as_str()),
            (8080, "/", "127.0.0.1:8080")
        );
        let u = Url::parse("http://[::1]:9/x").unwrap();
        assert_eq!(
            (u.host.as_str(), u.authority().as_str()),
            ("::1", "[::1]:9")
        );
        assert_eq!(Url::parse("http://h?q").unwrap().path, "/?q");
        assert!(Url::parse("ftp://x").is_err());
        assert!(Url::parse("http://").is_err());
    }

    #[test]
    fn host_port() {
        assert_eq!(split_host_port("a:1", 2), Some(("a".into(), 1)));
        assert_eq!(split_host_port("a", 2), Some(("a".into(), 2)));
        assert_eq!(split_host_port("[::1]", 2), Some(("::1".into(), 2)));
        assert_eq!(split_host_port("::1", 2), None);
        assert_eq!(split_host_port("a:x", 2), None);
    }
}
