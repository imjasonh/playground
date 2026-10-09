//! File-system state that a recorded run depends on: kinds, metadata,
//! content hashes, and directory listings, plus the checks that compare a
//! recorded expectation with the disk.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt};
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

/// Files larger than this are identified by size, mtime, and inode instead of
/// a content hash.
pub const LARGE_FILE: u64 = 256 << 20;

/// A content hash computed this long after the file's last change is trusted
/// on later lookups as long as the file's stat signature is unchanged. File
/// timestamps come from a coarse clock, so a write in the same tick as the
/// hash can leave mtime and ctime unchanged.
const RACY_MS: i64 = 2_000;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", content = "value", rename_all = "snake_case")]
pub enum Kind {
    Missing,
    File,
    Dir,
    Symlink(String),
    Fifo,
    Socket,
    CharDevice,
    BlockDevice,
    Error(i32),
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Missing => write!(f, "missing"),
            Kind::File => write!(f, "a file"),
            Kind::Dir => write!(f, "a directory"),
            Kind::Symlink(t) => write!(f, "a symlink to {t}"),
            Kind::Fifo => write!(f, "a FIFO"),
            Kind::Socket => write!(f, "a socket"),
            Kind::CharDevice => write!(f, "a character device"),
            Kind::BlockDevice => write!(f, "a block device"),
            Kind::Error(e) => write!(f, "inaccessible ({})", io::Error::from_raw_os_error(*e)),
        }
    }
}

/// The result of `stat` or `lstat` on a path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Meta {
    pub kind: Kind,
    pub mode: u32,
    pub size: u64,
    pub mtime_ns: i64,
    pub ctime_ns: i64,
    pub dev: u64,
    pub ino: u64,
}

impl Meta {
    /// Returns the state of `path`, following a final symlink if `follow`.
    pub fn of(path: &Path, follow: bool) -> Meta {
        let md = if follow {
            fs::metadata(path)
        } else {
            fs::symlink_metadata(path)
        };
        match md {
            Ok(md) => Meta::from_metadata(path, &md),
            Err(e) => Meta::from_error(&e),
        }
    }

    fn from_metadata(path: &Path, md: &fs::Metadata) -> Meta {
        let ft = md.file_type();
        let kind = if ft.is_file() {
            Kind::File
        } else if ft.is_dir() {
            Kind::Dir
        } else if ft.is_symlink() {
            let target = fs::read_link(path).unwrap_or_default();
            Kind::Symlink(target.to_string_lossy().into_owned())
        } else if ft.is_fifo() {
            Kind::Fifo
        } else if ft.is_socket() {
            Kind::Socket
        } else if ft.is_char_device() {
            Kind::CharDevice
        } else {
            Kind::BlockDevice
        };
        Meta {
            kind,
            mode: md.mode() & 0o7777,
            size: md.size(),
            mtime_ns: md.mtime() * 1_000_000_000 + md.mtime_nsec(),
            ctime_ns: md.ctime() * 1_000_000_000 + md.ctime_nsec(),
            dev: md.dev(),
            ino: md.ino(),
        }
    }

    fn from_error(e: &io::Error) -> Meta {
        let kind = match e.raw_os_error() {
            Some(libc::ENOENT) | Some(libc::ENOTDIR) => Kind::Missing,
            Some(code) => Kind::Error(code),
            None => Kind::Error(libc::EIO),
        };
        Meta {
            kind,
            mode: 0,
            size: 0,
            mtime_ns: 0,
            ctime_ns: 0,
            dev: 0,
            ino: 0,
        }
    }

    pub fn exists(&self) -> bool {
        !matches!(self.kind, Kind::Missing)
    }

    pub fn sig(&self, at_ms: i64) -> Sig {
        Sig {
            dev: self.dev,
            ino: self.ino,
            size: self.size,
            mtime_ns: self.mtime_ns,
            ctime_ns: self.ctime_ns,
            at_ms,
        }
    }

    /// Reports whether the file changed within the coarse timestamp window
    /// before `now_ms`, so an identical stat signature later doesn't prove
    /// identical content.
    pub fn is_racy(&self, now_ms: i64) -> bool {
        let newest = self.mtime_ns.max(self.ctime_ns) / 1_000_000;
        newest + RACY_MS > now_ms
    }
}

/// A stat signature recorded next to a content hash, so a later check can
/// skip rehashing a file that hasn't changed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Sig {
    pub dev: u64,
    pub ino: u64,
    pub size: u64,
    pub mtime_ns: i64,
    pub ctime_ns: i64,
    pub at_ms: i64,
}

impl Sig {
    fn matches(&self, m: &Meta) -> bool {
        self.dev == m.dev
            && self.ino == m.ino
            && self.size == m.size
            && self.mtime_ns == m.mtime_ns
            && self.ctime_ns == m.ctime_ns
            && !m.is_racy(self.at_ms)
    }
}

pub fn now_ms() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0)
}

/// Returns an identity for the content of the regular file at `path`: a
/// BLAKE3 hash, or size, mtime, and inode for files over [`LARGE_FILE`].
/// Fails if the path isn't a regular file or changed while it was read.
pub fn content_id(path: &Path) -> io::Result<(String, Meta)> {
    let f = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NONBLOCK)
        .open(path)?;
    let before = Meta::from_metadata(path, &f.metadata()?);
    if before.kind != Kind::File {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "not a regular file",
        ));
    }
    if before.size > LARGE_FILE {
        let id = format!("meta:{}:{}:{}", before.size, before.mtime_ns, before.ino);
        return Ok((id, before));
    }
    let hash = hash_reader(&f)?;
    let after = Meta::from_metadata(path, &f.metadata()?);
    if after.size != before.size
        || after.mtime_ns != before.mtime_ns
        || after.ctime_ns != before.ctime_ns
    {
        return Err(io::Error::other("file changed while it was hashed"));
    }
    Ok((hash, before))
}

fn hash_reader(mut f: &File) -> io::Result<String> {
    let mut hasher = blake3::Hasher::new();
    let mut buf = vec![0u8; 256 << 10];
    loop {
        let n = match f.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        };
        hasher.update(&buf[..n]);
    }
    Ok(hasher.finalize().to_hex().to_string())
}

#[cfg(test)]
pub fn hash_bytes(b: &[u8]) -> String {
    blake3::hash(b).to_hex().to_string()
}

/// A directory listing: entry names mapped to a one-letter kind.
pub type Listing = BTreeMap<Vec<u8>, char>;

pub fn read_listing(path: &Path) -> io::Result<Listing> {
    let mut out = Listing::new();
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let kind = match entry.file_type() {
            Ok(ft) => kind_letter(&ft),
            Err(_) => '?',
        };
        out.insert(entry.file_name().as_bytes().to_vec(), kind);
    }
    Ok(out)
}

fn kind_letter(ft: &fs::FileType) -> char {
    if ft.is_file() {
        'f'
    } else if ft.is_dir() {
        'd'
    } else if ft.is_symlink() {
        'l'
    } else if ft.is_fifo() {
        'p'
    } else if ft.is_socket() {
        's'
    } else if ft.is_char_device() {
        'c'
    } else if ft.is_block_device() {
        'b'
    } else {
        '?'
    }
}

/// Returns the one-letter listing kind for a [`Kind`] observed with `lstat`.
pub fn listing_letter(kind: &Kind) -> Option<char> {
    Some(match kind {
        Kind::Missing | Kind::Error(_) => return None,
        Kind::File => 'f',
        Kind::Dir => 'd',
        Kind::Symlink(_) => 'l',
        Kind::Fifo => 'p',
        Kind::Socket => 's',
        Kind::CharDevice => 'c',
        Kind::BlockDevice => 'b',
    })
}

pub fn listing_hash(listing: &Listing) -> String {
    let mut h = blake3::Hasher::new();
    for (name, kind) in listing {
        h.update(name);
        h.update(&[0, *kind as u8, b'\n']);
    }
    h.finalize().to_hex().to_string()
}

/// The state that a recorded path must still be in for a cached result to
/// be replayed. Only the attributes that the command observed, or that it
/// left behind as output, are set.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Expect {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<Kind>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mode: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub size: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mtime_ns: Option<i64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub listing: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sig: Option<Sig>,
}

impl Expect {
    pub fn kind(meta: &Meta) -> Expect {
        Expect {
            kind: Some(meta.kind.clone()),
            ..Expect::default()
        }
    }

    pub fn mode(meta: &Meta) -> Expect {
        let mut e = Expect::kind(meta);
        if meta.exists() && !matches!(meta.kind, Kind::Error(_)) {
            e.mode = Some(meta.mode);
        }
        e
    }

    /// Returns what `stat` reveals about a path. Directory sizes and mtimes
    /// are left out: they change whenever an entry changes, and programs that
    /// care about entries read the listing, which is checked separately.
    pub fn stat(meta: &Meta) -> Expect {
        let mut e = Expect::mode(meta);
        if meta.kind == Kind::File {
            e.size = Some(meta.size);
            e.mtime_ns = Some(meta.mtime_ns);
        }
        e
    }

    /// Adds every attribute of `other`. Fails if both set an attribute to
    /// different values.
    pub fn merge(&mut self, other: &Expect) -> Result<(), &'static str> {
        fn join<T: Clone + PartialEq>(
            a: &mut Option<T>,
            b: &Option<T>,
            what: &'static str,
        ) -> Result<(), &'static str> {
            match (a.as_ref(), b) {
                (Some(x), Some(y)) if x != y => Err(what),
                (None, Some(y)) => {
                    *a = Some(y.clone());
                    Ok(())
                }
                _ => Ok(()),
            }
        }
        join(&mut self.kind, &other.kind, "kind")?;
        join(&mut self.mode, &other.mode, "mode")?;
        join(&mut self.size, &other.size, "size")?;
        join(&mut self.mtime_ns, &other.mtime_ns, "modification time")?;
        join(&mut self.content, &other.content, "content")?;
        join(&mut self.listing, &other.listing, "listing")?;
        if self.sig.is_none() {
            self.sig = other.sig.clone();
        }
        Ok(())
    }

    /// Compares the expectation with the disk. Returns a description of the
    /// first difference, or `None` if `path` is still as expected.
    pub fn check(&self, path: &Path, follow: bool) -> Option<String> {
        let meta = Meta::of(path, follow);
        if let Some(k) = &self.kind {
            if *k != meta.kind {
                return Some(format!("was {k}, now {}", meta.kind));
            }
        }
        if let Some(m) = self.mode {
            if m != meta.mode {
                return Some(format!("mode changed from {m:o} to {:o}", meta.mode));
            }
        }
        if let Some(s) = self.size {
            if s != meta.size {
                return Some(format!("size changed from {s} to {}", meta.size));
            }
        }
        if let Some(t) = self.mtime_ns {
            if t != meta.mtime_ns {
                return Some("modification time changed".into());
            }
        }
        if let Some(want) = &self.content {
            let unchanged = self.sig.as_ref().is_some_and(|s| s.matches(&meta));
            if !unchanged {
                match content_id(path) {
                    Ok((got, _)) if got == *want => {}
                    Ok(_) => return Some("content changed".into()),
                    Err(e) => return Some(format!("content unreadable: {e}")),
                }
            }
        }
        if let Some(want) = &self.listing {
            match read_listing(path) {
                Ok(l) if listing_hash(&l) == *want => {}
                Ok(_) => return Some("directory entries changed".into()),
                Err(e) => return Some(format!("listing unreadable: {e}")),
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;

    #[test]
    fn kinds() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("f");
        fs::write(&f, "x").unwrap();
        let l = dir.path().join("l");
        symlink("f", &l).unwrap();
        assert_eq!(Meta::of(&f, true).kind, Kind::File);
        assert_eq!(Meta::of(dir.path(), true).kind, Kind::Dir);
        assert_eq!(Meta::of(&l, false).kind, Kind::Symlink("f".into()));
        assert_eq!(Meta::of(&l, true).kind, Kind::File);
        assert_eq!(Meta::of(&dir.path().join("nope"), true).kind, Kind::Missing);
        assert_eq!(Meta::of(&f.join("under-a-file"), true).kind, Kind::Missing);
    }

    #[test]
    fn content_id_tracks_bytes() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("f");
        fs::write(&f, "one").unwrap();
        let (a, _) = content_id(&f).unwrap();
        fs::write(&f, "two").unwrap();
        let (b, _) = content_id(&f).unwrap();
        fs::write(&f, "one").unwrap();
        let (c, _) = content_id(&f).unwrap();
        assert_ne!(a, b);
        assert_eq!(a, c);
        assert_eq!(a, hash_bytes(b"one"));
        assert!(content_id(dir.path()).is_err());
    }

    #[test]
    fn check_reports_changes() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("f");
        fs::write(&f, "one").unwrap();
        let (id, meta) = content_id(&f).unwrap();
        let e = Expect {
            kind: Some(Kind::File),
            content: Some(id),
            sig: Some(meta.sig(now_ms())),
            ..Expect::default()
        };
        assert_eq!(e.check(&f, true), None);
        fs::write(&f, "two").unwrap();
        assert_eq!(e.check(&f, true).as_deref(), Some("content changed"));
        fs::remove_file(&f).unwrap();
        assert_eq!(
            e.check(&f, true).as_deref(),
            Some("was a file, now missing")
        );
    }

    #[test]
    fn listing_ignores_order_but_not_names() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("b"), "").unwrap();
        fs::write(dir.path().join("a"), "").unwrap();
        let first = listing_hash(&read_listing(dir.path()).unwrap());
        let e = Expect {
            listing: Some(first.clone()),
            ..Expect::default()
        };
        assert_eq!(e.check(dir.path(), true), None);
        fs::create_dir(dir.path().join("c")).unwrap();
        assert!(e.check(dir.path(), true).is_some());
    }

    #[test]
    fn merge_detects_conflicts() {
        let mut a = Expect {
            kind: Some(Kind::File),
            ..Expect::default()
        };
        let b = Expect {
            kind: Some(Kind::File),
            content: Some("h".into()),
            ..Expect::default()
        };
        a.merge(&b).unwrap();
        assert_eq!(a.content.as_deref(), Some("h"));
        let c = Expect {
            content: Some("other".into()),
            ..Expect::default()
        };
        assert_eq!(a.merge(&c), Err("content"));
    }

    #[test]
    fn stat_skips_directory_times() {
        let dir = tempfile::tempdir().unwrap();
        let e = Expect::stat(&Meta::of(dir.path(), true));
        assert_eq!(e.size, None);
        assert_eq!(e.mtime_ns, None);
        fs::write(dir.path().join("new"), "").unwrap();
        assert_eq!(e.check(dir.path(), true), None);
    }
}
