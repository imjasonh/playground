//! The cache key: what must be identical for two invocations to share
//! cached results. Everything else the command depends on is checked against
//! the recorded inputs instead.

use std::ffi::OsString;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::path::{Path, PathBuf};

/// Environment variables that differ between shells and terminals without
/// changing what a command does. A program can't be observed reading an
/// environment variable, so every other variable is part of the key.
pub const NOISY_ENV: &[&str] = &[
    "_",
    "OLDPWD",
    "SHLVL",
    "TERM_SESSION_ID",
    "ITERM_SESSION_ID",
    "WINDOWID",
    "TMUX_PANE",
    "KITTY_WINDOW_ID",
    "WEZTERM_PANE",
    "SECURITYSESSIONID",
    "SSH_TTY",
    "SSH_CLIENT",
    "SSH_CONNECTION",
    "SSH_AUTH_SOCK",
    "GPG_TTY",
];

/// What memo's standard input is, which decides how the command's reads of
/// it are handled.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stdin {
    /// Closed or `/dev/null`: nothing to read.
    Null,
    /// A regular file, recorded as an input like any file the command reads.
    File(PathBuf),
    /// A terminal or pipe. A command that reads it can't be cached.
    Stream { tty: bool, dev: u64, ino: u64 },
}

impl Stdin {
    pub fn detect() -> Stdin {
        let Ok(md) = std::fs::metadata("/proc/self/fd/0") else {
            return Stdin::Null;
        };
        let ft = md.file_type();
        if ft.is_char_device() && md.rdev() == libc::makedev(1, 3) {
            return Stdin::Null;
        }
        if ft.is_file() {
            if let Ok(p) = std::fs::read_link("/proc/self/fd/0") {
                if p.is_absolute() && !p.as_os_str().as_bytes().ends_with(b" (deleted)") {
                    return Stdin::File(p);
                }
            }
        }
        Stdin::Stream {
            tty: crate::capture::isatty(0),
            dev: md.dev(),
            ino: md.ino(),
        }
    }

    fn key(&self) -> Vec<u8> {
        match self {
            Stdin::Null => b"null".to_vec(),
            Stdin::File(p) => [b"file:", p.as_os_str().as_bytes()].concat(),
            Stdin::Stream { tty: true, .. } => b"tty".to_vec(),
            Stdin::Stream { tty: false, .. } => b"stream".to_vec(),
        }
    }
}

/// Returns the environment that goes into the key, sorted, without
/// [`NOISY_ENV`], memo's own `MEMO_` settings, and `ignore`.
pub fn key_env(ignore: &[String]) -> Vec<(OsString, OsString)> {
    let mut env: Vec<(OsString, OsString)> = std::env::vars_os()
        .filter(|(k, _)| {
            let name = k.to_string_lossy();
            !name.starts_with("MEMO_")
                && !NOISY_ENV.contains(&name.as_ref())
                && !ignore.iter().any(|i| *i == name)
        })
        .collect();
    env.sort();
    env
}

pub struct Parts<'a> {
    pub argv: &'a [OsString],
    pub cwd: &'a Path,
    pub env: &'a [(OsString, OsString)],
    pub stdin: &'a Stdin,
    pub stdout_tty: bool,
    pub stderr_tty: bool,
    pub ignore: &'a [PathBuf],
    pub http: bool,
}

/// Hashes the parts with every field length-prefixed, so `["a b"]` and
/// `["a", "b"]` get different keys.
pub fn compute(p: &Parts) -> String {
    let mut h = blake3::Hasher::new();
    let mut field = |b: &[u8]| {
        h.update(&(b.len() as u64).to_le_bytes());
        h.update(b);
    };
    field(b"memo/v1");
    field(&(p.argv.len() as u64).to_le_bytes());
    for a in p.argv {
        field(a.as_bytes());
    }
    field(p.cwd.as_os_str().as_bytes());
    field(&(p.env.len() as u64).to_le_bytes());
    for (k, v) in p.env {
        field(k.as_bytes());
        field(v.as_bytes());
    }
    field(&p.stdin.key());
    field(&[p.stdout_tty as u8, p.stderr_tty as u8, p.http as u8]);
    field(&(p.ignore.len() as u64).to_le_bytes());
    for i in p.ignore {
        field(i.as_os_str().as_bytes());
    }
    h.finalize().to_hex().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(argv: &[&str], env: &[(&str, &str)]) -> String {
        let argv: Vec<OsString> = argv.iter().map(OsString::from).collect();
        let env: Vec<(OsString, OsString)> = env
            .iter()
            .map(|(k, v)| (OsString::from(k), OsString::from(v)))
            .collect();
        compute(&Parts {
            argv: &argv,
            cwd: Path::new("/work"),
            env: &env,
            stdin: &Stdin::Null,
            stdout_tty: false,
            stderr_tty: false,
            ignore: &[],
            http: false,
        })
    }

    #[test]
    fn fields_are_unambiguous() {
        assert_ne!(key(&["a b"], &[]), key(&["a", "b"], &[]));
        assert_ne!(key(&["ab"], &[]), key(&["a", "b"], &[]));
        assert_eq!(key(&["x"], &[("A", "1")]), key(&["x"], &[("A", "1")]));
        assert_ne!(key(&["x"], &[("A", "1")]), key(&["x"], &[("A", "2")]));
    }

    #[test]
    fn noisy_and_ignored_env_is_dropped() {
        let env = key_env(&["HOME".to_string()]);
        assert!(env.iter().all(|(k, _)| k != "HOME" && k != "OLDPWD"));
        assert!(env.windows(2).all(|w| w[0] <= w[1]));
    }
}
