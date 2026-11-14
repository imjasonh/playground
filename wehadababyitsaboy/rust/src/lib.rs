//! Records one use of a command-line program in the wehadababyitsaboy bucket.
//!
//! A ping is an HTTPS GET for an object that does not exist:
//!
//! ```text
//! https://storage.googleapis.com/wehadababyitsaboy/CLIENT/ARGS?bob=wehadababyitsaboy&arch=ARCH&os=OS&v=VERSION
//! ```
//!
//! The bucket answers 403, and its hourly usage logs keep the request line, the
//! client address, and the user agent. `CLIENT` is the program name. `ARGS` is
//! the subcommand and the names of the flags the user set, joined with dots. A
//! ping never carries a flag value or a positional argument, because a value
//! can be a path, a query, or a token.
//!
//! The crate works with programs built on clap. Parse the arguments with
//! [`parse`] in place of `Parser::parse`.
//!
//! Set `DO_NOT_TRACK=1` or `WHBIAB_DISABLE=1` to turn pings off. A debug build
//! sends nothing unless `WHBIAB_ENDPOINT` names a server, so `cargo run` and
//! `cargo test` never count as usage.

use std::env;
use std::thread::{self, JoinHandle};
use std::time::Duration;

use clap::Parser;

mod clap_parts;

const DEFAULT_ENDPOINT: &str = "https://storage.googleapis.com/wehadababyitsaboy";
const MAX_PARTS: usize = 16;
const MAX_PART_LEN: usize = 64;
/// The object name of a ping that has no subcommand and no flags.
const DEFAULT_ARGS: &str = "run";
/// Bounds one ping, from connecting to reading the response.
const TIMEOUT: Duration = Duration::from_secs(2);

/// A ping in flight. Dropping it waits for the request, which takes at most
/// about two seconds, so keep it alive until the program is done.
#[must_use = "bind the ping to a variable; dropping it at once waits for the request"]
pub struct Ping {
    handle: Option<JoinHandle<()>>,
}

impl Ping {
    /// Waits for the request. Call it before `std::process::exit`, which skips
    /// destructors.
    pub fn wait(self) {
        drop(self);
    }
}

impl Drop for Ping {
    fn drop(&mut self) {
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

/// Parses the program's arguments, as `P::parse()` does, and sends a ping in
/// the background for the command that runs.
///
/// `CLIENT` is the clap command's name. `ARGS` is the subcommands the user ran
/// and the long names of the flags they set, sorted. `version` is the
/// program's version, normally `env!("CARGO_PKG_VERSION")`.
///
/// ```ignore
/// let (cli, _ping) = whbiab::parse::<Cli>(env!("CARGO_PKG_VERSION"));
/// ```
///
/// Like `P::parse()`, this exits for `--help`, `--version`, and arguments that
/// don't parse, and it sends nothing then. A disabled or failed ping is silent.
pub fn parse<P: Parser>(version: &str) -> (P, Ping) {
    let cmd = P::command();
    let matches = cmd.clone().get_matches();
    let parsed = P::from_arg_matches(&matches).unwrap_or_else(|e| e.exit());
    let parts = clap_parts::clap_parts(&cmd, &matches);
    let cfg = Config::from_lookup(|key| env::var(key).ok());
    let ping = track_with(&cfg, cmd.get_name(), version, &parts);
    (parsed, ping)
}

#[derive(Debug, Default)]
struct Config {
    endpoint: Option<String>,
    ci: bool,
    disabled: bool,
}

impl Config {
    fn from_lookup(get: impl Fn(&str) -> Option<String>) -> Self {
        let on = |key: &str| {
            get(key).is_some_and(|v| !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false"))
        };
        Config {
            endpoint: get("WHBIAB_ENDPOINT").filter(|v| !v.is_empty()),
            ci: on("CI"),
            disabled: on("DO_NOT_TRACK") || on("WHBIAB_DISABLE"),
        }
    }
}

fn track_with(cfg: &Config, client: &str, version: &str, parts: &[String]) -> Ping {
    let none = Ping { handle: None };
    if cfg.disabled || (cfg!(debug_assertions) && cfg.endpoint.is_none()) {
        return none;
    }
    let Some(url) = ping_url(cfg, client, version, parts) else {
        return none;
    };
    let agent = format!("{}/{} (whbiab)", clean(client), version);
    let handle = thread::Builder::new()
        .name("whbiab".into())
        .spawn(move || send(&url, &agent))
        .ok();
    Ping { handle }
}

fn send(url: &str, agent: &str) {
    let agent = ureq::AgentBuilder::new()
        .timeout(TIMEOUT)
        .user_agent(agent)
        .build();
    // The bucket answers 403 on purpose, and ureq reports that as an error.
    // Only the request matters.
    let _ = agent.get(url).call();
}

fn ping_url(cfg: &Config, client: &str, version: &str, parts: &[String]) -> Option<String> {
    let name = clean(client);
    if name.is_empty() {
        return None;
    }
    let mut args: Vec<String> = parts
        .iter()
        .map(|p| clean(p))
        .filter(|p| !p.is_empty())
        .take(MAX_PARTS)
        .collect();
    if args.is_empty() {
        args.push(DEFAULT_ARGS.to_owned());
    }

    let base = cfg.endpoint.as_deref().unwrap_or(DEFAULT_ENDPOINT);
    let mut url = format!(
        "{}/{}/{}?bob=wehadababyitsaboy&arch={}",
        base.trim_end_matches('/'),
        name,
        args.join("."),
        encode(&arch()),
    );
    if cfg.ci {
        url.push_str("&ci=1");
    }
    url.push_str(&format!(
        "&os={}&v={}",
        encode(env::consts::OS),
        encode(version)
    ));
    Some(url)
}

/// Names the architecture the way Go's `GOARCH` does, so that Go and Rust
/// programs group together.
fn arch() -> String {
    match env::consts::ARCH {
        "x86_64" => "amd64".to_owned(),
        "aarch64" => "arm64".to_owned(),
        other => other.to_owned(),
    }
}

/// Lowercases `s` and replaces every character that is not safe in an object
/// name with `-`.
fn clean(s: &str) -> String {
    let mapped: String = s
        .to_lowercase()
        .chars()
        .map(|c| match c {
            'a'..='z' | '0'..='9' | '-' | '_' => c,
            _ => '-',
        })
        .collect();
    let trimmed = mapped.trim_matches('-');
    let cut = &trimmed[..trimmed.len().min(MAX_PART_LEN)];
    cut.trim_matches('-').to_owned()
}

/// Percent-encodes everything but unreserved characters.
fn encode(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for b in s.bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' => {
                out.push(b as char)
            }
            _ => out.push_str(&format!("%{b:02X}")),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::io::{BufRead, BufReader, Read, Write};
    use std::net::TcpListener;
    use std::sync::mpsc;
    use std::time::Instant;

    fn lookup(pairs: &[(&str, &str)]) -> impl Fn(&str) -> Option<String> {
        let map: HashMap<String, String> = pairs
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect();
        move |key| map.get(key).cloned()
    }

    fn cfg(endpoint: &str) -> Config {
        Config {
            endpoint: Some(endpoint.to_owned()),
            ..Config::default()
        }
    }

    /// Serves one request with a 403 and sends its request line and headers on
    /// the channel.
    fn serve_once() -> (String, mpsc::Receiver<Vec<String>>) {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut reader = BufReader::new(stream.try_clone().unwrap());
            let mut lines = Vec::new();
            loop {
                let mut line = String::new();
                if reader.read_line(&mut line).unwrap() == 0 {
                    break;
                }
                let line = line.trim_end().to_owned();
                if line.is_empty() {
                    break;
                }
                lines.push(line);
            }
            stream
                .write_all(
                    b"HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\nConnection: close\r\n\r\n",
                )
                .unwrap();
            let _ = tx.send(lines);
        });
        (format!("http://{addr}/wehadababyitsaboy"), rx)
    }

    #[test]
    fn sends_a_ping() {
        let (endpoint, rx) = serve_once();

        track_with(
            &cfg(&endpoint),
            "My CLI",
            "1.2.3",
            &["Query".into(), "max_width".into(), "a/b".into()],
        )
        .wait();

        let lines = rx.recv_timeout(Duration::from_secs(5)).unwrap();
        let request = &lines[0];
        assert!(
            request.starts_with(
                "GET /wehadababyitsaboy/my-cli/query.max_width.a-b?bob=wehadababyitsaboy&arch="
            ),
            "request line = {request}"
        );
        assert!(request.contains("&os="), "request line = {request}");
        assert!(
            request.contains("&v=1.2.3 HTTP/1.1"),
            "request line = {request}"
        );
        let agent = lines
            .iter()
            .find(|l| l.to_lowercase().starts_with("user-agent:"))
            .map(|l| l.split_once(':').unwrap().1.trim())
            .unwrap_or_default();
        assert_eq!(agent, "my-cli/1.2.3 (whbiab)");
    }

    #[test]
    fn marks_ci_runs() {
        let config = Config {
            ci: true,
            ..cfg("http://example.test/b")
        };
        let url = ping_url(&config, "tool", "1.0.0", &[]).unwrap();
        assert!(url.contains("&ci=1&os="), "url = {url}");
        let url = ping_url(&cfg("http://example.test/b"), "tool", "1.0.0", &[]).unwrap();
        assert!(!url.contains("ci="), "url = {url}");
    }

    #[test]
    fn names_a_ping_with_no_parts_run() {
        let url = ping_url(&cfg("http://example.test/b/"), "tool", "1.0.0", &[]).unwrap();
        assert!(
            url.starts_with("http://example.test/b/tool/run?bob=wehadababyitsaboy&"),
            "url = {url}"
        );
    }

    #[test]
    fn encodes_the_version() {
        let url = ping_url(&cfg("http://example.test/b"), "tool", "1.0.0+dirty", &[]).unwrap();
        assert!(url.ends_with("&v=1.0.0%2Bdirty"), "url = {url}");
    }

    #[test]
    fn skips_an_empty_client() {
        assert_eq!(
            ping_url(
                &cfg("http://example.test/b"),
                " // ",
                "1.0.0",
                &["query".into()]
            ),
            None
        );
    }

    #[test]
    fn bounds_the_parts() {
        let parts = vec!["flag".to_owned(); 40];
        let url = ping_url(&cfg("http://example.test/b"), "tool", "1.0.0", &parts).unwrap();
        let path = url.split('?').next().unwrap();
        assert_eq!(path.matches("flag").count(), MAX_PARTS, "path = {path}");
    }

    #[test]
    fn opt_out_values() {
        for (pairs, disabled) in [
            (vec![("DO_NOT_TRACK", "1")], true),
            (vec![("DO_NOT_TRACK", "yes")], true),
            (vec![("DO_NOT_TRACK", "0")], false),
            (vec![("DO_NOT_TRACK", "false")], false),
            (vec![("DO_NOT_TRACK", "")], false),
            (vec![("WHBIAB_DISABLE", "1")], true),
            (vec![("WHBIAB_DISABLE", "0")], false),
            (vec![], false),
        ] {
            let config = Config::from_lookup(lookup(&pairs));
            assert_eq!(config.disabled, disabled, "{pairs:?}");
        }
    }

    #[test]
    fn reads_the_endpoint_and_ci() {
        let config = Config::from_lookup(lookup(&[
            ("WHBIAB_ENDPOINT", "http://x.test"),
            ("CI", "true"),
        ]));
        assert_eq!(config.endpoint.as_deref(), Some("http://x.test"));
        assert!(config.ci);
        let config = Config::from_lookup(lookup(&[("WHBIAB_ENDPOINT", ""), ("CI", "0")]));
        assert_eq!(config.endpoint, None);
        assert!(!config.ci);
    }

    #[test]
    fn a_disabled_ping_sends_nothing() {
        let config = Config {
            disabled: true,
            ..cfg("http://127.0.0.1:1")
        };
        assert!(track_with(&config, "tool", "1.0.0", &[]).handle.is_none());
    }

    #[test]
    fn a_debug_build_sends_nothing_without_an_endpoint() {
        let ping = track_with(&Config::default(), "tool", "1.0.0", &[]);
        assert!(ping.handle.is_none());
    }

    #[test]
    fn an_unreachable_endpoint_is_silent() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        drop(listener);

        let start = Instant::now();
        track_with(&cfg(&format!("http://{addr}")), "tool", "1.0.0", &[]).wait();

        assert!(start.elapsed() < Duration::from_secs(5));
    }

    #[test]
    fn a_hanging_endpoint_times_out() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut buf = [0u8; 1024];
            while stream.read(&mut buf).unwrap_or(0) > 0 {}
        });

        let start = Instant::now();
        track_with(&cfg(&format!("http://{addr}")), "tool", "1.0.0", &[]).wait();

        assert!(start.elapsed() < TIMEOUT + Duration::from_secs(3));
    }

    #[test]
    fn clean_table() {
        for (input, want) in [
            ("query", "query"),
            ("Query", "query"),
            ("max_width", "max_width"),
            ("no-renames", "no-renames"),
            ("a b", "a-b"),
            ("a/b", "a-b"),
            ("a.b", "a-b"),
            ("../etc/passwd", "etc-passwd"),
            ("SELECT * FROM t", "select---from-t"),
            ("héllo", "h-llo"),
            ("--", ""),
            ("", ""),
        ] {
            assert_eq!(clean(input), want, "clean({input:?})");
        }
        assert_eq!(clean(&"a".repeat(100)), "a".repeat(MAX_PART_LEN));
    }
}
