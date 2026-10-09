//! Command-line parsing and the run, explain, and clear commands.

use crate::cache::{self, Entry, LastRun, Store};
use crate::capture::{self, Capture, MAX_OUTPUT};
use crate::fsstate::now_ms;
use crate::key::{self, Stdin};
use crate::record::{par_map, Event, Known, Recorder, Role};
use crate::trace;
use std::ffi::OsString;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const USAGE: &str = "\
Usage:
  memo [OPTIONS] [--] COMMAND [ARGS...]
  memo explain [OPTIONS] [--] COMMAND [ARGS...]
  memo clear
  memo help

Runs COMMAND and records the files it reads, the directories it lists, and the
files it writes. A later call with the same command, directory, environment,
and standard input replays the recorded output and exit status, as long as
those inputs are unchanged and the written files are still as COMMAND left
them. Linux only.

Options:
  --ttl DURATION     expire results after DURATION (for example 90s, 30m, 12h,
                     or 7d), and cache runs whose network access memo can't
                     check
  --refresh          run COMMAND even if a cached result applies
  --cache-failures   cache and replay runs that exit with a nonzero status
  --ignore PATH      don't record files under PATH (repeatable)
  --ignore-env NAME  leave environment variable NAME out of the cache key
                     (repeatable)
  -v, --verbose      report hits, misses, and why a run wasn't cached

Commands:
  explain            report whether a cached result would be replayed, and why
                     not; exits 0 if one would be
  clear              delete all cached results
  help, --help       show this help

Results live in $MEMO_CACHE_DIR, or in memo under $XDG_CACHE_HOME or ~/.cache.
";

#[derive(Debug, Default)]
struct Opts {
    ttl: Option<Duration>,
    refresh: bool,
    cache_failures: bool,
    ignore: Vec<PathBuf>,
    ignore_env: Vec<String>,
    verbose: bool,
    argv: Vec<OsString>,
}

#[derive(Debug)]
enum Cmd {
    Run(Opts),
    Explain(Opts),
    Clear,
    Help,
}

macro_rules! note {
    ($($arg:tt)*) => { eprintln!("memo: {}", format!($($arg)*)) };
}

pub fn main(args: Vec<OsString>) -> i32 {
    match parse(args) {
        Ok(Cmd::Help) => {
            print!("{USAGE}");
            0
        }
        Ok(Cmd::Clear) => clear(),
        Ok(Cmd::Run(o)) => run(&o),
        Ok(Cmd::Explain(o)) => explain(&o),
        Err(e) => {
            note!("{e}");
            eprintln!("Run 'memo --help' for usage.");
            2
        }
    }
}

fn parse(args: Vec<OsString>) -> Result<Cmd, String> {
    let mut it = args.into_iter().peekable();
    let explain = match it.peek().and_then(|a| a.to_str()) {
        Some("explain") => {
            it.next();
            true
        }
        Some("clear") => {
            it.next();
            return match it.next() {
                None => Ok(Cmd::Clear),
                Some(_) => Err("clear takes no arguments".into()),
            };
        }
        Some("help" | "--help" | "-h") => return Ok(Cmd::Help),
        _ => false,
    };
    let mut o = Opts::default();
    while let Some(arg) = it.next() {
        let Some(s) = arg.to_str() else {
            o.argv.push(arg);
            break;
        };
        let (flag, inline) = match s.split_once('=') {
            Some((f, v)) if f.starts_with("--") => (f, Some(OsString::from(v))),
            _ => (s, None),
        };
        let mut value = |name: &str| -> Result<OsString, String> {
            inline
                .clone()
                .or_else(|| it.next())
                .ok_or_else(|| format!("{name} needs a value"))
        };
        match flag {
            "--" => break,
            "--ttl" => {
                let v = value("--ttl")?;
                o.ttl = Some(parse_duration(&v.to_string_lossy())?);
            }
            "--ignore" => o.ignore.push(PathBuf::from(value("--ignore")?)),
            "--ignore-env" => o
                .ignore_env
                .push(value("--ignore-env")?.to_string_lossy().into_owned()),
            "--refresh" => o.refresh = true,
            "--cache-failures" => o.cache_failures = true,
            "-v" | "--verbose" => o.verbose = true,
            "-h" | "--help" => return Ok(Cmd::Help),
            _ if s.starts_with('-') && s.len() > 1 => return Err(format!("unknown option {s}")),
            _ => {
                o.argv.push(arg);
                break;
            }
        }
    }
    o.argv.extend(it);
    if o.argv.is_empty() {
        return Err("no command given".into());
    }
    Ok(if explain {
        Cmd::Explain(o)
    } else {
        Cmd::Run(o)
    })
}

/// Parses durations like `90s`, `30m`, `1h30m`, `12h`, `7d`, or `500ms`.
fn parse_duration(s: &str) -> Result<Duration, String> {
    let bad = || format!("invalid duration {s:?} (want for example 90s, 30m, 12h, or 7d)");
    let mut total = 0f64;
    let mut rest = s;
    if rest.is_empty() {
        return Err(bad());
    }
    while !rest.is_empty() {
        let n_end = rest
            .find(|c: char| !(c.is_ascii_digit() || c == '.'))
            .unwrap_or(rest.len());
        let n: f64 = rest[..n_end].parse().map_err(|_| bad())?;
        rest = &rest[n_end..];
        let u_end = rest
            .find(|c: char| c.is_ascii_digit() || c == '.')
            .unwrap_or(rest.len());
        let unit = match &rest[..u_end] {
            "ms" => 0.001,
            "s" => 1.0,
            "m" => 60.0,
            "h" => 3600.0,
            "d" => 86400.0,
            _ => return Err(bad()),
        };
        total += n * unit;
        rest = &rest[u_end..];
    }
    if total <= 0.0 || !total.is_finite() {
        return Err(bad());
    }
    Ok(Duration::from_secs_f64(total))
}

/// Formats how long ago `ms` was, in the largest whole unit.
fn ago(ms: i64) -> String {
    span(now_ms() - ms)
}

/// Formats a duration in milliseconds in the largest whole unit.
fn span(ms: i64) -> String {
    let s = ms.max(0) / 1000;
    match s {
        0..60 => format!("{s}s"),
        60..3600 => format!("{}m", s / 60),
        3600..86400 => format!("{}h", s / 3600),
        _ => format!("{}d", s / 86400),
    }
}

struct Ctx {
    cwd: PathBuf,
    stdin: Stdin,
    key: String,
    ignore: Vec<PathBuf>,
    store: Store,
}

/// Kernel interfaces, plus files that tools rewrite on every run without it
/// affecting their results: Go's telemetry counters and npm's debug logs.
fn default_ignores(cwd: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = ["/proc", "/sys", "/dev"].map(PathBuf::from).to_vec();
    if let Some(home) = std::env::var_os("HOME").filter(|h| !h.is_empty()) {
        for p in [".config/go/telemetry", ".npm/_logs"] {
            out.push(absolute(cwd, &Path::new(&home).join(p)));
        }
    }
    out
}

fn absolute(cwd: &Path, p: &Path) -> PathBuf {
    let p = cwd.join(p);
    std::fs::canonicalize(&p).unwrap_or_else(|_| p.components().collect())
}

fn context(o: &Opts) -> Result<Ctx, String> {
    let cwd =
        std::env::current_dir().map_err(|e| format!("can't find the working directory: {e}"))?;
    let root = cache::default_dir().ok_or("can't find a cache directory; set MEMO_CACHE_DIR")?;
    let store = Store::open(root).map_err(|e| format!("can't open the cache: {e}"))?;
    let stdin = Stdin::detect();
    let user_ignore: Vec<PathBuf> = o.ignore.iter().map(|p| absolute(&cwd, p)).collect();
    let env = key::key_env(&o.ignore_env);
    let key = key::compute(&key::Parts {
        argv: &o.argv,
        cwd: &cwd,
        env: &env,
        stdin: &stdin,
        stdout_tty: capture::isatty(1),
        stderr_tty: capture::isatty(2),
        ignore: &user_ignore,
    });
    let mut ignore = default_ignores(&cwd);
    ignore.extend(user_ignore);
    ignore.push(absolute(&cwd, store.root()));
    Ok(Ctx {
        cwd,
        stdin,
        key,
        ignore,
        store,
    })
}

fn run(o: &Opts) -> i32 {
    let ctx = match context(o) {
        Ok(ctx) => ctx,
        Err(e) => {
            note!("{e}; running without the cache");
            return run_plain(o);
        }
    };
    if !o.refresh {
        match lookup(&ctx.store, &ctx.key, o) {
            Lookup::Hit { entry, chunks } => {
                if o.verbose {
                    note!(
                        "replaying the result recorded {} ago ({} paths unchanged)",
                        ago(entry.created_ms),
                        entry.paths.len()
                    );
                }
                capture::replay(&chunks);
                return entry.exit_code;
            }
            Lookup::Miss(why) => {
                if o.verbose {
                    note!("running: {why}");
                }
            }
        }
    }
    record(o, &ctx)
}

fn run_plain(o: &Opts) -> i32 {
    match Command::new(&o.argv[0]).args(&o.argv[1..]).status() {
        Ok(s) => s.code().unwrap_or_else(|| 128 + s.signal().unwrap_or(0)),
        Err(e) => spawn_failed(o, &e),
    }
}

fn spawn_failed(o: &Opts, e: &std::io::Error) -> i32 {
    note!("{}: {e}", o.argv[0].to_string_lossy());
    if e.kind() == std::io::ErrorKind::NotFound {
        127
    } else {
        126
    }
}

enum Lookup {
    Hit {
        entry: Entry,
        chunks: Vec<(u8, Vec<u8>)>,
    },
    Miss(String),
}

/// Returns every recorded path that no longer matches, with what changed.
fn changes(entry: &Entry) -> Vec<String> {
    par_map(&entry.paths, |p| {
        p.check().map(|d| format!("{}: {d}", p.path))
    })
    .into_iter()
    .flatten()
    .collect()
}

/// Returns why `entry` can't be replayed, or `None` if it can.
fn unusable(entry: &Entry, o: &Opts) -> Option<String> {
    if entry.expires_ms.is_some_and(|t| t <= now_ms()) {
        return Some("the cached result expired".into());
    }
    if entry.exit_code != 0 && !o.cache_failures {
        return Some(format!(
            "the cached result exited with status {}; pass --cache-failures to replay it",
            entry.exit_code
        ));
    }
    changes(entry).into_iter().next()
}

fn lookup(store: &Store, key: &str, o: &Opts) -> Lookup {
    let mut why = None;
    for id in store.ids(key) {
        let Some(entry) = store.load(key, &id) else {
            continue;
        };
        match unusable(&entry, o) {
            None => match store.output(key, &id).and_then(|b| capture::decode(&b)) {
                Ok(chunks) => return Lookup::Hit { entry, chunks },
                Err(e) => {
                    why.get_or_insert(format!("the cached output is unreadable: {e}"));
                }
            },
            Some(r) => {
                why.get_or_insert(r);
            }
        }
    }
    Lookup::Miss(why.unwrap_or_else(|| match store.last(key) {
        Some(last) if !last.cached && !last.reasons.is_empty() => {
            format!("the last run wasn't cached: {}", last.reasons[0])
        }
        _ => "no cached result".into(),
    }))
}

fn exit_code(status: i32) -> (i32, Option<i32>) {
    if libc::WIFEXITED(status) {
        (libc::WEXITSTATUS(status), None)
    } else if libc::WIFSIGNALED(status) {
        let sig = libc::WTERMSIG(status);
        (128 + sig, Some(sig))
    } else {
        (1, None)
    }
}

/// Collects the content hashes that earlier results for the key recorded.
fn known_hashes(store: &Store, key: &str) -> Known {
    let mut known = Known::new();
    for (_, entry) in store.entries(key) {
        for p in entry.paths {
            if let (Some(content), Some(sig)) = (p.expect.content, p.expect.sig) {
                known.entry(PathBuf::from(p.path)).or_insert((sig, content));
            }
        }
    }
    known
}

fn record(o: &Opts, ctx: &Ctx) -> i32 {
    let mut recorder = Recorder::new(ctx.ignore.clone(), None);
    recorder.reuse(known_hashes(&ctx.store, &ctx.key));
    let stdin_id = match &ctx.stdin {
        Stdin::File(path) => {
            recorder.apply(Event::Open {
                path: path.clone(),
                flags: libc::O_RDONLY,
            });
            None
        }
        Stdin::Stream { dev, ino, .. } => Some((*dev, *ino)),
        Stdin::Null => None,
    };
    let (cap, io) = match Capture::start() {
        Ok(x) => x,
        Err(e) => {
            note!("can't capture output ({e}); running without the cache");
            return run_plain(o);
        }
    };
    let mut cmd = Command::new(&o.argv[0]);
    cmd.args(&o.argv[1..])
        .stdout(Stdio::from(io.stdout))
        .stderr(Stdio::from(io.stderr));
    let started = Instant::now();
    let started_ms = now_ms();
    let fin = match trace::run(cmd, stdin_id, recorder) {
        Ok(fin) => fin,
        Err(trace::Error::Setup(e)) => {
            cap.finish(None);
            if e.raw_os_error() == Some(libc::EBUSY) {
                note!("an outer memo or another seccomp supervisor already traces this process; running without the cache");
            } else {
                note!("can't trace commands on this system ({e}); running without the cache");
            }
            return run_plain(o);
        }
        Err(trace::Error::Spawn(e)) => {
            cap.finish(None);
            return spawn_failed(o, &e);
        }
    };
    let captured = cap.finish(fin.lingering.then_some(Duration::from_millis(200)));
    let duration_ms = started.elapsed().as_millis() as u64;
    let (code, signal) = exit_code(fin.status);
    let outcome = fin.outcome;

    let mut reasons = outcome.reasons.clone();
    if let Some(sig) = signal {
        reasons.push(format!("was killed by signal {sig}"));
    } else if code != 0 && !o.cache_failures {
        reasons.push(format!(
            "exited with status {code}; pass --cache-failures to cache failures"
        ));
    }
    if captured.overflow {
        reasons.push(format!("printed more than {} MiB", MAX_OUTPUT >> 20));
    }
    if captured.broken_pipe {
        reasons.push("couldn't print all of its output because the reader closed the pipe".into());
    }
    if !outcome.net.is_empty() && o.ttl.is_none() {
        let shown: Vec<&str> = outcome.net.iter().take(3).map(String::as_str).collect();
        let more = outcome.net.len() - shown.len();
        let more = if more > 0 {
            format!(" and {more} more")
        } else {
            String::new()
        };
        reasons.push(format!(
            "{}{more}; memo can't tell whether a server's answer changed, so pass --ttl to cache it for a fixed time",
            shown.join(", ")
        ));
    }

    let cached = reasons.is_empty();
    if cached {
        let entry = Entry {
            version: 1,
            created_ms: started_ms,
            expires_ms: o.ttl.map(|t| started_ms + t.as_millis() as i64),
            argv: o
                .argv
                .iter()
                .map(|a| a.to_string_lossy().into_owned())
                .collect(),
            cwd: ctx.cwd.to_string_lossy().into_owned(),
            exit_code: code,
            duration_ms,
            paths: outcome.paths,
            net: outcome.net,
        };
        if let Err(e) = ctx
            .store
            .save(&ctx.key, &entry, &capture::encode(&captured.chunks))
        {
            note!("couldn't save the result: {e}");
        } else if o.verbose {
            let inputs = entry
                .paths
                .iter()
                .filter(|p| p.role != Role::Output)
                .count();
            let outputs = entry.paths.iter().filter(|p| p.role != Role::Input).count();
            note!(
                "cached the result: {inputs} inputs, {outputs} outputs, {} traced calls",
                outcome.events
            );
        }
    } else if o.verbose {
        note!("not cached: {}", reasons.join("; "));
    }
    let last = LastRun {
        at_ms: now_ms(),
        exit_code: code,
        cached,
        reasons,
    };
    let _ = ctx.store.save_last(&ctx.key, &last);
    code
}

fn explain(o: &Opts) -> i32 {
    let ctx = match context(o) {
        Ok(ctx) => ctx,
        Err(e) => {
            note!("{e}");
            return 2;
        }
    };
    println!("key: {}", ctx.key);
    let entries = ctx.store.entries(&ctx.key);
    if entries.is_empty() {
        println!("no cached results");
    }
    let mut fresh = false;
    for (i, (_, e)) in entries.iter().enumerate() {
        let inputs = e.paths.iter().filter(|p| p.role != Role::Output).count();
        let outputs = e.paths.iter().filter(|p| p.role != Role::Input).count();
        let expiry = match e.expires_ms {
            Some(t) if t > now_ms() => format!(", expires in {}", span(t - now_ms())),
            Some(_) => ", expired".to_string(),
            None => String::new(),
        };
        println!(
            "result {}: recorded {} ago, exit status {}, {inputs} inputs, {outputs} outputs{expiry}",
            i + 1,
            ago(e.created_ms),
            e.exit_code
        );
        let found = changes(e);
        match unusable(e, o) {
            None => {
                fresh = true;
                println!("  would be replayed");
            }
            Some(why) if found.is_empty() => println!("  not replayed: {why}"),
            Some(_) => {
                println!("  stale:");
                for c in found.iter().take(20) {
                    println!("    {c}");
                }
                if found.len() > 20 {
                    println!("    and {} more", found.len() - 20);
                }
            }
        }
        for n in &e.net {
            println!("  allowed by --ttl: {n}");
        }
        if o.verbose {
            for p in &e.paths {
                let role = match p.role {
                    Role::Input => "input ",
                    Role::Output => "output",
                    Role::Both => "both  ",
                };
                println!(
                    "    {role} {}{}",
                    p.path,
                    if p.follow { "" } else { " (link)" }
                );
            }
        }
    }
    if let Some(last) = ctx.store.last(&ctx.key) {
        println!(
            "last run: {} ago, exit status {}, {}",
            ago(last.at_ms),
            last.exit_code,
            if last.cached { "cached" } else { "not cached" }
        );
        for r in &last.reasons {
            println!("  {r}");
        }
    }
    if fresh {
        0
    } else {
        1
    }
}

fn clear() -> i32 {
    let Some(root) = cache::default_dir() else {
        note!("can't find a cache directory; set MEMO_CACHE_DIR");
        return 1;
    };
    match Store::open(root).and_then(|s| s.clear().map(|_| s)) {
        Ok(s) => {
            println!("cleared {}", s.root().display());
            0
        }
        Err(e) => {
            note!("can't clear the cache: {e}");
            1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(a: &[&str]) -> Vec<OsString> {
        a.iter().map(OsString::from).collect()
    }

    #[test]
    fn parses_options_and_command() {
        let Ok(Cmd::Run(o)) = parse(args(&["--ttl", "1h30m", "-v", "--ignore=/tmp", "ls", "-l"]))
        else {
            panic!("expected a run");
        };
        assert_eq!(o.ttl, Some(Duration::from_secs(5400)));
        assert!(o.verbose);
        assert_eq!(o.ignore, vec![PathBuf::from("/tmp")]);
        assert_eq!(o.argv, args(&["ls", "-l"]));

        let Ok(Cmd::Run(o)) = parse(args(&["--", "--weird-name"])) else {
            panic!("expected a run");
        };
        assert_eq!(o.argv, args(&["--weird-name"]));

        let Ok(Cmd::Explain(o)) = parse(args(&["explain", "--", "explain"])) else {
            panic!("expected explain");
        };
        assert_eq!(o.argv, args(&["explain"]));

        assert!(matches!(parse(args(&["clear"])), Ok(Cmd::Clear)));
        assert!(matches!(parse(args(&["--help"])), Ok(Cmd::Help)));
        assert!(parse(args(&[])).is_err());
        assert!(parse(args(&["--nope", "ls"])).is_err());
        assert!(parse(args(&["--ttl"])).is_err());
    }

    #[test]
    fn durations() {
        assert_eq!(parse_duration("90s"), Ok(Duration::from_secs(90)));
        assert_eq!(parse_duration("7d"), Ok(Duration::from_secs(7 * 86400)));
        assert_eq!(parse_duration("500ms"), Ok(Duration::from_millis(500)));
        assert!(parse_duration("10").is_err());
        assert!(parse_duration("0s").is_err());
        assert!(parse_duration("1w").is_err());
        assert!(parse_duration("").is_err());
    }
}
