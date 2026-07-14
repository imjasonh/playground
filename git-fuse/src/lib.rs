//! git-fuse: a read-only FUSE adapter for `git-server`.
//!
//! Mount layout:
//!
//! ```text
//! <mount>/refs/<ref>            file containing "<sha>\n" (e.g. refs/heads/main)
//! <mount>/refs/HEAD             sha of the default branch
//! <mount>/commits/<sha>/<path>  the tree of any commit, as plain files
//! ```
//!
//! Reads are served from whichever source answers first:
//!
//! * a **shared local bare-repo cache** (one per remote URL), read through a
//!   persistent `git cat-file --batch-command` process — microseconds once
//!   objects are local;
//! * the remote's **JSON read API** (`/api/<repo>/refs`, `/tree/…`, `/file/…`)
//!   for anything not local yet — one HTTP round-trip, no clone required.
//!
//! At mount time a background thread warms the cache with a shallow
//! (`--depth=1`) fetch and then deepens to a full fetch; until it finishes,
//! reads fall through to the remote API, so first-byte latency never waits on
//! a clone. After a push to the remote, the periodic ref refresh notices the
//! new head and triggers an incremental fetch.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

/// Crate-wide verbose flag; set once at mount from [`Options::verbose`].
pub(crate) static VERBOSE: AtomicBool = AtomicBool::new(false);

macro_rules! vlog {
    ($($t:tt)*) => {
        if crate::VERBOSE.load(std::sync::atomic::Ordering::Relaxed) {
            eprintln!("[git-fuse] {}", format!($($t)*));
        }
    };
}
pub(crate) use vlog;

mod cache;
mod fs;
mod remote;
mod source;
pub mod testutil;

use cache::{LocalCache, WarmState, STATE_SHALLOW, STATE_WARM};
use remote::Remote;
use source::Source;

/// Mount configuration.
pub struct Options {
    /// The git-server repo URL, e.g. `https://host/<repo>` — the same URL
    /// `git clone` would take. The JSON API base is derived from it.
    pub remote_url: String,
    /// Local bare-repo cache directory. Defaults to
    /// `$XDG_CACHE_HOME/git-fuse/<repo>-<hash>.git`, shared by every mount
    /// of the same remote.
    pub cache_dir: Option<PathBuf>,
    /// How long a refs snapshot stays fresh before the next `/refs` lookup
    /// re-queries the remote.
    pub refs_ttl: Duration,
    /// Byte budget for the in-memory blob LRU.
    pub blob_cache_bytes: usize,
    /// Warm the local cache in the background (shallow fetch, then full,
    /// then incremental on new pushes). Disable to serve purely from the
    /// remote API plus whatever the cache already holds.
    pub warmup: bool,
    /// Log FUSE-level activity to stderr.
    pub verbose: bool,
    /// Pass `allow_other` to the mount (requires `user_allow_other` in
    /// `/etc/fuse.conf`).
    pub allow_other: bool,
}

impl Options {
    pub fn new(remote_url: impl Into<String>) -> Self {
        Options {
            remote_url: remote_url.into(),
            cache_dir: None,
            refs_ttl: Duration::from_secs(2),
            blob_cache_bytes: 256 << 20,
            warmup: true,
            verbose: false,
            allow_other: false,
        }
    }
}

/// A live mount. Dropping it unmounts.
pub struct Mount {
    // Field order matters: the session must unmount before anything else
    // (e.g. a TempDir mountpoint in tests) is torn down.
    session: fuser::BackgroundSession,
    warm: Arc<WarmState>,
    /// The resolved cache directory (useful when it was defaulted).
    pub cache_dir: PathBuf,
}

impl Mount {
    /// Wait until the shallow fetch has landed (HEAD's tree is local).
    pub fn wait_local_usable(&self, timeout: Duration) -> bool {
        self.warm.wait_at_least(STATE_SHALLOW, timeout)
    }

    /// Wait until the full fetch has landed (all history local).
    pub fn wait_warm(&self, timeout: Duration) -> bool {
        self.warm.wait_at_least(STATE_WARM, timeout)
    }

    /// Block until the filesystem is unmounted (e.g. by `fusermount -u`).
    pub fn join(self) {
        self.session.join()
    }
}

/// Derive the default shared cache directory for a remote URL.
fn default_cache_dir(remote_url: &str) -> PathBuf {
    let base = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let home = std::env::var_os("HOME").map(PathBuf::from).unwrap_or_else(|| {
                std::env::temp_dir()
            });
            home.join(".cache")
        })
        .join("git-fuse");
    let stem: String = remote_url
        .trim_end_matches('/')
        .rsplit('/')
        .next()
        .unwrap_or("repo")
        .chars()
        .filter(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-'))
        .take(48)
        .collect();
    base.join(format!("{stem}-{:016x}.git", fnv1a64(remote_url.as_bytes())))
}

/// FNV-1a, used only to key cache directories by remote URL.
fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// Mount `opts.remote_url` at `mountpoint` and return a handle. The mount is
/// served on a background thread; drop the handle (or call
/// [`Mount::join`]) to control its lifetime.
pub fn mount(mountpoint: &Path, opts: Options) -> Result<Mount, String> {
    VERBOSE.store(opts.verbose, Ordering::Relaxed);
    let cache_dir = opts
        .cache_dir
        .clone()
        .unwrap_or_else(|| default_cache_dir(&opts.remote_url));
    let remote = Remote::new(&opts.remote_url)?;
    let cache = LocalCache::open(&cache_dir, &opts.remote_url, opts.warmup)?;
    let warm = cache.warm.clone();
    let source = Source::new(cache, remote, opts.refs_ttl, opts.blob_cache_bytes);
    let filesystem = fs::GitFuse::new(source, opts.refs_ttl);

    let mut options = vec![
        fuser::MountOption::RO,
        fuser::MountOption::FSName(opts.remote_url.clone()),
        fuser::MountOption::Subtype("git-fuse".to_string()),
        // Kernel-side attribute/entry caching honors the per-reply TTLs the
        // filesystem sets (long for immutable commit data, short for refs).
        fuser::MountOption::DefaultPermissions,
    ];
    if opts.allow_other {
        options.push(fuser::MountOption::AllowOther);
    }
    let session = fuser::spawn_mount2(filesystem, mountpoint, &options)
        .map_err(|e| format!("mount at {} failed: {e}", mountpoint.display()))?;
    Ok(Mount {
        session,
        warm,
        cache_dir,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_cache_dir_is_stable_and_distinct() {
        let a = default_cache_dir("http://h/repo");
        let b = default_cache_dir("http://h/repo");
        let c = default_cache_dir("http://h/other");
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(a.to_string_lossy().contains("repo-"));
        assert!(a.to_string_lossy().ends_with(".git"));
    }
}
