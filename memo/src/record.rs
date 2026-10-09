//! Turns the file-system events of a traced run into the expectations that a
//! cached result depends on.
//!
//! An input is state that the command observed before changing it: content it
//! read, metadata it queried, or a directory it listed. An output is the state
//! of a path that the command changed, taken after the run. A cached result is
//! replayed only while every input is unchanged and every output is still as
//! the run left it. A run is stored only if that already holds right after
//! the run; otherwise the entry could never be used.

use crate::fsstate::{
    content_id, listing_hash, listing_letter, now_ms, read_listing, Expect, Kind, Meta, Sig,
};
use crate::net::NetTarget;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs::File;
use std::io::{self, Read};
use std::net::SocketAddr;
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};

/// A file-system or network operation that a traced process started. Paths
/// are absolute. Events are applied while the process is still blocked at
/// the start of the system call, so the recorder sees the state before the
/// call takes effect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Open {
        path: PathBuf,
        flags: i32,
    },
    Stat {
        path: PathBuf,
        follow: bool,
    },
    Access {
        path: PathBuf,
        follow: bool,
    },
    Readlink {
        path: PathBuf,
    },
    Exec {
        path: PathBuf,
    },
    List {
        path: PathBuf,
    },
    Chdir {
        path: PathBuf,
    },
    Truncate {
        path: PathBuf,
        len: i64,
    },
    Rename {
        from: PathBuf,
        to: PathBuf,
    },
    /// `unlink` or `rmdir`.
    Remove {
        path: PathBuf,
    },
    /// `mkdir`, `mknod`, `symlink`, or the new name of `link`.
    Create {
        path: PathBuf,
    },
    /// `chmod`, `chown`, or `utimes`.
    SetAttr {
        path: PathBuf,
    },
    /// `connect`, or `sendto` or `sendmsg` with an address. Unix socket paths
    /// are already absolute.
    Net(NetTarget),
    StdinRead,
    Unsupported(String),
}

const KIND_F: u8 = 1;
const KIND_NF: u8 = 1 << 1;
const MODE_F: u8 = 1 << 2;
const MODE_NF: u8 = 1 << 3;
const STAT_F: u8 = 1 << 4;
const STAT_NF: u8 = 1 << 5;
const CONTENT: u8 = 1 << 6;
const LIST: u8 = 1 << 7;
const FOLLOWS: u8 = KIND_F | MODE_F | STAT_F | CONTENT | LIST;
const METADATA: u8 = KIND_F | KIND_NF | MODE_F | MODE_NF | STAT_F | STAT_NF;

/// Unix sockets whose servers only answer user and host lookups or take
/// logs. Connecting to them doesn't make a run depend on another process.
const QUIET_SOCKETS: &[&str] = &[
    "/run/systemd/journal/",
    "/run/systemd/userdb/",
    "/run/nscd/",
    "/var/run/nscd/",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Role {
    Input,
    Output,
    Both,
}

/// What one path must look like for a cached result to be replayed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PathExpect {
    pub path: String,
    pub follow: bool,
    pub role: Role,
    #[serde(flatten)]
    pub expect: Expect,
}

impl PathExpect {
    pub fn check(&self) -> Option<String> {
        self.expect.check(Path::new(&self.path), self.follow)
    }
}

#[derive(Debug, Default)]
pub struct Outcome {
    pub paths: Vec<PathExpect>,
    /// Why the run can't be cached at all.
    pub reasons: Vec<String>,
    /// Network or IPC access that memo can't verify later. A run with only
    /// these can still be cached for a fixed time.
    pub net: Vec<String>,
    pub events: u64,
}

struct Rec {
    pre_nf: Meta,
    pre_f: Option<Meta>,
    obs: u8,
    content: Option<String>,
    content_sig: Option<Sig>,
    content_pending: bool,
    listing: Option<String>,
    written: bool,
}

impl Rec {
    fn new(path: &Path) -> Rec {
        Rec {
            pre_nf: Meta::of(path, false),
            pre_f: None,
            obs: 0,
            content: None,
            content_sig: None,
            content_pending: false,
            listing: None,
            written: false,
        }
    }

    fn pre_f(&mut self, path: &Path) -> &Meta {
        if self.pre_f.is_none() {
            let m = if matches!(self.pre_nf.kind, Kind::Symlink(_)) {
                Meta::of(path, true)
            } else {
                self.pre_nf.clone()
            };
            self.pre_f = Some(m);
        }
        self.pre_f.as_ref().expect("set above")
    }

    fn hash_now(&mut self, path: &Path) -> Result<(), String> {
        let (id, meta) =
            content_id(path).map_err(|e| format!("{}: could not hash it: {e}", path.display()))?;
        self.content = Some(id);
        self.content_sig = Some(meta.sig(now_ms()));
        Ok(())
    }
}

/// Content hashes from earlier runs, keyed by path, with the stat signature
/// that each was computed for.
pub type Known = HashMap<PathBuf, (Sig, String)>;

/// Returns the content identity of `path`, reusing a hash from `known` if
/// the file is provably unchanged since then.
fn hash_with(path: &Path, known: &Known) -> io::Result<(String, Meta)> {
    if let Some((sig, id)) = known.get(path) {
        let meta = Meta::of(path, true);
        if sig.matches(&meta) {
            return Ok((id.clone(), meta));
        }
    }
    content_id(path)
}

pub struct Recorder {
    recs: HashMap<PathBuf, Rec>,
    written_children: HashMap<PathBuf, Vec<PathBuf>>,
    ignore: Vec<PathBuf>,
    proxy: Option<SocketAddr>,
    known: Known,
    reasons: BTreeSet<String>,
    net: BTreeSet<String>,
    events: u64,
}

impl Recorder {
    /// Creates a recorder that skips paths under any of `ignore` and
    /// connections to `proxy`.
    pub fn new(ignore: Vec<PathBuf>, proxy: Option<SocketAddr>) -> Recorder {
        Recorder {
            recs: HashMap::new(),
            written_children: HashMap::new(),
            ignore,
            proxy,
            known: Known::new(),
            reasons: BTreeSet::new(),
            net: BTreeSet::new(),
            events: 0,
        }
    }

    /// Supplies hashes from earlier runs, so unchanged files aren't hashed
    /// again.
    pub fn reuse(&mut self, known: Known) {
        self.known = known;
    }

    pub fn add_reason(&mut self, reason: impl Into<String>) {
        self.reasons.insert(reason.into());
    }

    pub fn add_net(&mut self, what: impl Into<String>) {
        self.net.insert(what.into());
    }

    fn ignored(&self, path: &Path) -> bool {
        self.ignore.iter().any(|p| path.starts_with(p))
    }

    pub fn apply(&mut self, ev: Event) {
        self.events += 1;
        match ev {
            Event::Open { path, flags } => self.open(&path, flags),
            Event::Stat { path, follow } => {
                self.observe(&path, if follow { STAT_F } else { STAT_NF })
            }
            Event::Access { path, follow } => {
                self.observe(&path, if follow { MODE_F } else { MODE_NF })
            }
            Event::Readlink { path } => self.observe(&path, KIND_NF),
            Event::Exec { path } => self.exec(path),
            Event::List { path } => self.observe(&path, LIST),
            Event::Chdir { path } => self.observe(&path, KIND_F),
            Event::Truncate { path, len } => {
                if len != 0 {
                    self.observe(&path, CONTENT);
                }
                self.write(&path);
            }
            Event::Rename { from, to } => self.rename(&from, &to),
            Event::Remove { path } | Event::Create { path } | Event::SetAttr { path } => {
                self.write(&path)
            }
            Event::Net(target) => self.connect(target),
            Event::StdinRead => self.add_reason(
                "read standard input, which memo can't fingerprint when it's a terminal or a pipe",
            ),
            Event::Unsupported(what) => self.add_reason(what),
        }
    }

    fn open(&mut self, path: &Path, flags: i32) {
        let follow = flags & libc::O_NOFOLLOW == 0;
        if flags & libc::O_PATH != 0 {
            self.observe(path, if follow { KIND_F } else { KIND_NF });
            return;
        }
        if flags & libc::O_TMPFILE == libc::O_TMPFILE {
            self.observe(path, KIND_F);
            return;
        }
        if !follow {
            self.observe(path, KIND_NF);
            if self
                .recs
                .get(path)
                .is_some_and(|r| matches!(r.pre_nf.kind, Kind::Symlink(_)))
            {
                return;
            }
        }
        let writes = flags & libc::O_ACCMODE != libc::O_RDONLY
            || flags & (libc::O_CREAT | libc::O_TRUNC) != 0;
        if !writes {
            self.observe(path, CONTENT);
            return;
        }
        // Without O_TRUNC or O_EXCL the result depends on the old content:
        // appending, editing in place, or opening a lock file.
        if flags & (libc::O_TRUNC | libc::O_EXCL) == 0 {
            self.observe(path, CONTENT);
        }
        self.write(path);
    }

    fn exec(&mut self, path: PathBuf) {
        self.observe(&path, CONTENT);
        // The kernel opens the script interpreter or ELF loader itself, so
        // those reads never show up as system calls.
        let mut cur = path;
        for _ in 0..4 {
            match interpreter(&cur) {
                Some(next) => {
                    self.observe(&next, CONTENT);
                    cur = next;
                }
                None => break,
            }
        }
    }

    fn rename(&mut self, from: &Path, to: &Path) {
        if !self.ignored(from) && Meta::of(from, false).kind == Kind::Dir {
            let moved: Vec<PathBuf> = self
                .recs
                .keys()
                .filter(|p| p.starts_with(from) && *p != from)
                .cloned()
                .collect();
            for old in moved {
                let new = to.join(old.strip_prefix(from).expect("filtered by prefix"));
                self.write(&old);
                self.write(&new);
            }
        }
        self.write(from);
        self.write(to);
    }

    fn connect(&mut self, target: NetTarget) {
        match target {
            NetTarget::Inet(addr) => {
                if Some(addr) != self.proxy {
                    self.add_net(format!("connected to {addr}"));
                }
            }
            NetTarget::Unix(path) => {
                let path = PathBuf::from(std::ffi::OsStr::from_bytes(&path));
                if self.ignored(&path) {
                    return;
                }
                self.observe(&path, KIND_F);
                let is_socket = self
                    .recs
                    .get(&path)
                    .and_then(|r| r.pre_f.as_ref())
                    .is_some_and(|m| m.kind == Kind::Socket);
                let quiet = path
                    .to_str()
                    .is_some_and(|p| QUIET_SOCKETS.iter().any(|q| p.starts_with(q)));
                if is_socket && !quiet {
                    self.add_net(format!("connected to the Unix socket {}", path.display()));
                }
            }
            NetTarget::Abstract(name) => {
                self.add_net(format!("connected to the abstract Unix socket @{name}"))
            }
            NetTarget::Netlink | NetTarget::Unspecified => {}
            NetTarget::Other(family) => {
                self.add_net(format!("used a socket of address family {family}"))
            }
        }
    }

    fn observe(&mut self, path: &Path, obs: u8) {
        if self.ignored(path) {
            return;
        }
        let rec = self
            .recs
            .entry(path.to_path_buf())
            .or_insert_with(|| Rec::new(path));
        if rec.written {
            return;
        }
        rec.obs |= obs;
        if obs & FOLLOWS == 0 {
            return;
        }
        let kind = rec.pre_f(path).kind.clone();
        if obs & CONTENT != 0 && kind == Kind::File && rec.content.is_none() && !rec.content_pending
        {
            if rec.pre_f(path).is_racy(now_ms()) {
                if let Err(e) = rec.hash_now(path) {
                    self.reasons.insert(e);
                }
            } else {
                rec.content_pending = true;
            }
        }
        let wants_listing = obs & LIST != 0 && kind == Kind::Dir && rec.listing.is_none();
        if wants_listing {
            match self.pre_run_listing(path) {
                Ok(l) => self.recs.get_mut(path).expect("inserted above").listing = Some(l),
                Err(e) => {
                    self.reasons.insert(e);
                }
            }
        }
    }

    fn write(&mut self, path: &Path) {
        if self.ignored(path) {
            return;
        }
        let rec = self
            .recs
            .entry(path.to_path_buf())
            .or_insert_with(|| Rec::new(path));
        if rec.content_pending {
            rec.content_pending = false;
            if let Err(e) = rec.hash_now(path) {
                self.reasons.insert(e);
            }
        }
        if !rec.written {
            rec.written = true;
            if let Some(parent) = path.parent() {
                self.written_children
                    .entry(parent.to_path_buf())
                    .or_default()
                    .push(path.to_path_buf());
            }
        }
    }

    /// Lists `dir` as it was before the run: entries that the command
    /// already created are dropped, and entries it already removed are put
    /// back.
    fn pre_run_listing(&self, dir: &Path) -> Result<String, String> {
        let mut listing =
            read_listing(dir).map_err(|e| format!("{}: could not list it: {e}", dir.display()))?;
        for kid in self.written_children.get(dir).into_iter().flatten() {
            let Some(name) = kid.file_name() else {
                continue;
            };
            match listing_letter(&self.recs[kid].pre_nf.kind) {
                Some(c) => {
                    listing.insert(name.as_bytes().to_vec(), c);
                }
                None => {
                    listing.remove(name.as_bytes());
                }
            }
        }
        Ok(listing_hash(&listing))
    }

    /// Computes the inputs and outputs of the finished run.
    pub fn finish(mut self) -> Outcome {
        let pending: Vec<PathBuf> = self
            .recs
            .iter()
            .filter(|(_, r)| r.content_pending)
            .map(|(p, _)| p.clone())
            .collect();
        let hashed = par_map(&pending, |path| {
            let pre = self.recs[path].pre_f.clone().expect("content observed");
            let same = |m: &Meta| m.sig(0) == pre.sig(0);
            if !same(&Meta::of(path, true)) {
                return Err(format!("{} changed while the command ran", path.display()));
            }
            match hash_with(path, &self.known) {
                Ok((id, meta)) if same(&meta) => Ok((id, meta.sig(now_ms()))),
                Ok(_) => Err(format!("{} changed while the command ran", path.display())),
                Err(e) => Err(format!("{}: could not hash it: {e}", path.display())),
            }
        });
        for (path, result) in pending.iter().zip(hashed) {
            let rec = self.recs.get_mut(path).expect("listed above");
            rec.content_pending = false;
            match result {
                Ok((id, sig)) => {
                    rec.content = Some(id);
                    rec.content_sig = Some(sig);
                }
                Err(e) => {
                    self.reasons.insert(e);
                }
            }
        }

        let dirs_with_writes: HashSet<&PathBuf> = self.written_children.keys().collect();
        let mut items: Vec<(&PathBuf, &Rec)> = self.recs.iter().collect();
        items.sort_by(|a, b| a.0.cmp(b.0));
        let results = par_map(&items, |(path, rec)| {
            expectations(path, rec, dirs_with_writes.contains(path), &self.known)
        });
        let mut paths = Vec::new();
        for r in results {
            match r {
                Ok(mut p) => paths.append(&mut p),
                Err(e) => {
                    self.reasons.insert(e);
                }
            }
        }
        Outcome {
            paths,
            reasons: self.reasons.into_iter().collect(),
            net: self.net.into_iter().collect(),
            events: self.events,
        }
    }
}

/// Builds the expectations for one path, checking that every input still
/// holds after the run.
fn expectations(
    path: &Path,
    rec: &Rec,
    has_written_children: bool,
    known: &Known,
) -> Result<Vec<PathExpect>, String> {
    let display = path.display();
    let Some(name) = path.to_str() else {
        return Err(format!("{display}: the path isn't valid UTF-8"));
    };
    let mut by_follow: BTreeMap<bool, (Expect, bool, bool)> = BTreeMap::new();
    let mut add = |follow: bool, e: Expect, input: bool| -> Result<(), String> {
        let slot = by_follow
            .entry(follow)
            .or_insert_with(|| (Expect::default(), false, false));
        slot.0
            .merge(&e)
            .map_err(|what| format!("{display}: conflicting {what} after the run"))?;
        if input {
            slot.1 = true;
        } else {
            slot.2 = true;
        }
        Ok(())
    };

    // A command often stats its own outputs before replacing them (rm -r,
    // cp, make), so metadata observations of a path it changes aren't inputs.
    let obs = if rec.written {
        rec.obs & !METADATA
    } else {
        rec.obs
    };
    let mut inputs: Vec<(bool, Expect)> = Vec::new();
    if obs & KIND_NF != 0 {
        inputs.push((false, Expect::kind(&rec.pre_nf)));
    }
    if obs & MODE_NF != 0 {
        inputs.push((false, Expect::mode(&rec.pre_nf)));
    }
    if obs & STAT_NF != 0 {
        inputs.push((false, Expect::stat(&rec.pre_nf)));
    }
    if let Some(pre_f) = &rec.pre_f {
        if obs & KIND_F != 0 {
            inputs.push((true, Expect::kind(pre_f)));
        }
        if obs & MODE_F != 0 {
            inputs.push((true, Expect::mode(pre_f)));
        }
        if obs & STAT_F != 0 {
            inputs.push((true, Expect::stat(pre_f)));
        }
        if obs & CONTENT != 0 {
            let mut e = Expect::kind(pre_f);
            if pre_f.kind == Kind::File {
                e.content = rec.content.clone();
                e.sig = rec.content_sig.clone();
                if e.content.is_none() {
                    return Err(format!("{display}: no content hash was recorded"));
                }
            }
            inputs.push((true, e));
        }
        if obs & LIST != 0 {
            let mut e = Expect::kind(pre_f);
            if pre_f.kind == Kind::Dir {
                e.listing = rec.listing.clone();
            }
            inputs.push((true, e));
        }
    }
    for (follow, e) in inputs {
        if let Some(diff) = e.check(path, follow) {
            return Err(if rec.written {
                format!("{display}: the command changed it after reading it ({diff})")
            } else if e.listing.is_some() && has_written_children {
                format!("{display}: the command added or removed entries in a directory it lists ({diff})")
            } else {
                format!("{display} changed while the command ran ({diff})")
            });
        }
        add(follow, e, true)?;
    }

    if rec.written {
        let post = Meta::of(path, false);
        let mut e = Expect::kind(&post);
        match &post.kind {
            Kind::File => {
                let (id, m) = hash_with(path, known)
                    .map_err(|err| format!("{display}: could not hash the output: {err}"))?;
                e.content = Some(id);
                e.mode = Some(m.mode);
                e.sig = Some(m.sig(now_ms()));
            }
            Kind::Dir => e.mode = Some(post.mode),
            Kind::Symlink(_) => {
                let target = Meta::of(path, true);
                let mut ef = Expect::kind(&target);
                if target.kind == Kind::File {
                    let (id, m) = hash_with(path, known)
                        .map_err(|err| format!("{display}: could not hash the output: {err}"))?;
                    ef.content = Some(id);
                    ef.sig = Some(m.sig(now_ms()));
                }
                add(true, ef, false)?;
            }
            _ => {}
        }
        add(false, e, false)?;
    }

    Ok(by_follow
        .into_iter()
        .map(|(follow, (expect, input, output))| PathExpect {
            path: name.to_string(),
            follow,
            role: match (input, output) {
                (true, true) => Role::Both,
                (true, false) => Role::Input,
                _ => Role::Output,
            },
            expect,
        })
        .collect())
}

/// Maps `f` over `items` on all available cores, keeping the order.
pub fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    if items.len() < 32 || threads < 2 {
        return items.iter().map(&f).collect();
    }
    let chunk = items.len().div_ceil(threads);
    std::thread::scope(|s| {
        let handles: Vec<_> = items
            .chunks(chunk)
            .map(|c| s.spawn(|| c.iter().map(&f).collect::<Vec<R>>()))
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("worker panicked"))
            .collect()
    })
}

/// Returns the program that the kernel loads to run the file at `path`: the
/// `#!` interpreter of a script, or the dynamic loader of an ELF binary.
pub fn interpreter(path: &Path) -> Option<PathBuf> {
    let mut f = File::open(path).ok()?;
    let mut buf = vec![0u8; 64 << 10];
    let mut n = 0;
    while n < buf.len() {
        match f.read(&mut buf[n..]) {
            Ok(0) => break,
            Ok(k) => n += k,
            Err(_) => return None,
        }
    }
    let buf = &buf[..n];
    let raw = if let Some(rest) = buf.strip_prefix(b"#!") {
        let line = &rest[..rest.len().min(254)];
        let line = line.split(|&c| c == b'\n').next()?;
        line.split(|c| c.is_ascii_whitespace())
            .find(|t| !t.is_empty())?
            .to_vec()
    } else {
        elf_interp(buf)?
    };
    if !raw.starts_with(b"/") {
        return None;
    }
    Some(PathBuf::from(std::ffi::OsStr::from_bytes(&raw)))
}

fn elf_interp(b: &[u8]) -> Option<Vec<u8>> {
    if b.len() < 52 || &b[..4] != b"\x7fELF" {
        return None;
    }
    let wide = b[4] == 2;
    let le = b[5] == 1;
    let num = |off: usize, len: usize| -> Option<u64> {
        let s = b.get(off..off.checked_add(len)?)?;
        let mut v = 0u64;
        for i in 0..len {
            let byte = if le { s[len - 1 - i] } else { s[i] };
            v = (v << 8) | byte as u64;
        }
        Some(v)
    };
    let (phoff, phentsize, phnum) = if wide {
        (num(32, 8)?, num(54, 2)?, num(56, 2)?)
    } else {
        (num(28, 4)?, num(42, 2)?, num(44, 2)?)
    };
    for i in 0..phnum {
        let off = usize::try_from(phoff.checked_add(i.checked_mul(phentsize)?)?).ok()?;
        if num(off, 4)? != 3 {
            continue;
        }
        let (start, len) = if wide {
            (num(off + 8, 8)?, num(off + 32, 8)?)
        } else {
            (num(off + 4, 4)?, num(off + 16, 4)?)
        };
        let start = usize::try_from(start).ok()?;
        let s = b.get(start..start.checked_add(usize::try_from(len).ok()?)?)?;
        return Some(s.split(|&c| c == 0).next()?.to_vec());
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn rec() -> Recorder {
        Recorder::new(vec![PathBuf::from("/proc")], None)
    }

    fn open_read(p: &Path) -> Event {
        Event::Open {
            path: p.to_path_buf(),
            flags: libc::O_RDONLY,
        }
    }

    fn expect_for<'a>(o: &'a Outcome, p: &Path, follow: bool) -> &'a PathExpect {
        o.paths
            .iter()
            .find(|e| Path::new(&e.path) == p && e.follow == follow)
            .unwrap_or_else(|| panic!("no expectation for {}: {:#?}", p.display(), o.paths))
    }

    #[test]
    fn read_becomes_content_input() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("in.txt");
        fs::write(&f, "hello").unwrap();
        let mut r = rec();
        r.apply(open_read(&f));
        let o = r.finish();
        assert!(o.reasons.is_empty(), "{:?}", o.reasons);
        let e = expect_for(&o, &f, true);
        assert_eq!(e.role, Role::Input);
        assert_eq!(
            e.expect.content.as_deref(),
            Some(crate::fsstate::hash_bytes(b"hello").as_str())
        );
        assert_eq!(e.check(), None);
        fs::write(&f, "changed").unwrap();
        assert!(e.check().is_some());
    }

    #[test]
    fn missing_file_is_an_input() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("config.toml");
        let mut r = rec();
        r.apply(open_read(&f));
        let o = r.finish();
        let e = expect_for(&o, &f, true);
        assert_eq!(e.expect.kind, Some(Kind::Missing));
        fs::write(&f, "").unwrap();
        assert_eq!(e.check().as_deref(), Some("was missing, now a file"));
    }

    #[test]
    fn truncating_write_is_an_output() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("out.txt");
        let mut r = rec();
        r.apply(Event::Open {
            path: f.clone(),
            flags: libc::O_WRONLY | libc::O_CREAT | libc::O_TRUNC,
        });
        fs::write(&f, "result").unwrap();
        let o = r.finish();
        assert!(o.reasons.is_empty(), "{:?}", o.reasons);
        let e = expect_for(&o, &f, false);
        assert_eq!(e.role, Role::Output);
        assert_eq!(e.check(), None);
        fs::remove_file(&f).unwrap();
        assert!(e.check().is_some());
    }

    #[test]
    fn appending_to_what_it_read_is_not_cacheable() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("log");
        fs::write(&f, "one\n").unwrap();
        let mut r = rec();
        r.apply(Event::Open {
            path: f.clone(),
            flags: libc::O_WRONLY | libc::O_CREAT | libc::O_APPEND,
        });
        fs::write(&f, "one\ntwo\n").unwrap();
        let o = r.finish();
        assert_eq!(o.reasons.len(), 1, "{:?}", o.reasons);
        assert!(
            o.reasons[0].contains("changed it after reading it"),
            "{:?}",
            o.reasons
        );
    }

    #[test]
    fn rewriting_the_same_content_is_cacheable() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("lock");
        fs::write(&f, "").unwrap();
        let mut r = rec();
        r.apply(Event::Open {
            path: f.clone(),
            flags: libc::O_RDWR | libc::O_CREAT,
        });
        fs::write(&f, "").unwrap();
        let o = r.finish();
        assert!(o.reasons.is_empty(), "{:?}", o.reasons);
        assert_eq!(expect_for(&o, &f, true).role, Role::Input);
        assert_eq!(expect_for(&o, &f, false).role, Role::Output);
    }

    #[test]
    fn external_change_during_run_is_not_cacheable() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("in");
        fs::write(&f, "old").unwrap();
        let mut r = rec();
        r.apply(Event::Stat {
            path: f.clone(),
            follow: true,
        });
        fs::write(&f, "newer content").unwrap();
        let o = r.finish();
        assert!(
            o.reasons
                .iter()
                .any(|x| x.contains("changed while the command ran")),
            "{:?}",
            o.reasons
        );
    }

    #[test]
    fn temporary_entries_dont_spoil_a_listing() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("a"), "").unwrap();
        let tmp = dir.path().join("tmp");
        let mut r = rec();
        r.apply(Event::Open {
            path: tmp.clone(),
            flags: libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL,
        });
        fs::write(&tmp, "").unwrap();
        r.apply(Event::List {
            path: dir.path().to_path_buf(),
        });
        r.apply(Event::Remove { path: tmp.clone() });
        fs::remove_file(&tmp).unwrap();
        let o = r.finish();
        assert!(o.reasons.is_empty(), "{:?}", o.reasons);
        let e = expect_for(&o, dir.path(), true);
        assert_eq!(e.check(), None);
        fs::write(dir.path().join("b"), "").unwrap();
        assert!(e.check().is_some());
    }

    #[test]
    fn new_entries_in_a_listed_directory_wait_for_the_next_run() {
        let dir = tempfile::tempdir().unwrap();
        let mut r = rec();
        r.apply(Event::List {
            path: dir.path().to_path_buf(),
        });
        let out = dir.path().join("out");
        r.apply(Event::Create { path: out.clone() });
        fs::create_dir(&out).unwrap();
        let o = r.finish();
        assert!(
            o.reasons.iter().any(|x| x.contains("directory it lists")),
            "{:?}",
            o.reasons
        );
    }

    #[test]
    fn network_and_ignored_paths() {
        let proxy: SocketAddr = "127.0.0.1:9".parse().unwrap();
        let mut r = Recorder::new(vec![PathBuf::from("/proc")], Some(proxy));
        r.apply(Event::Net(NetTarget::Inet(proxy)));
        r.apply(Event::Net(NetTarget::Inet("10.0.0.1:443".parse().unwrap())));
        r.apply(open_read(Path::new("/proc/self/status")));
        let o = r.finish();
        assert_eq!(o.net, vec!["connected to 10.0.0.1:443".to_string()]);
        assert!(o.paths.is_empty());
    }

    #[test]
    fn known_hashes_are_reused_only_for_unchanged_files() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("big-binary");
        fs::write(&f, "v1").unwrap();
        let meta = Meta::of(&f, true);
        let known_at = |at_ms| Known::from([(f.clone(), (meta.sig(at_ms), "reused".to_string()))]);
        // A hash taken right after the last change might predate a write in
        // the same timestamp tick, so it isn't trusted.
        let racy = known_at(now_ms());
        assert_eq!(
            hash_with(&f, &racy).unwrap().0,
            crate::fsstate::hash_bytes(b"v1")
        );
        let settled = known_at(now_ms() + 3_000);
        assert_eq!(hash_with(&f, &settled).unwrap().0, "reused");
        fs::write(&f, "v2!").unwrap();
        assert_eq!(
            hash_with(&f, &settled).unwrap().0,
            crate::fsstate::hash_bytes(b"v2!")
        );
    }

    #[test]
    fn script_interpreter_is_an_input() {
        let dir = tempfile::tempdir().unwrap();
        let script = dir.path().join("run");
        fs::write(&script, "#!/bin/sh -e\necho hi\n").unwrap();
        assert_eq!(interpreter(&script), Some(PathBuf::from("/bin/sh")));
        let mut r = rec();
        r.apply(Event::Exec {
            path: script.clone(),
        });
        let o = r.finish();
        assert!(
            o.paths.iter().any(|e| e.path == "/bin/sh"),
            "{:#?}",
            o.paths
        );
    }

    #[test]
    fn elf_loader() {
        let sh = fs::canonicalize("/bin/sh").unwrap();
        let loader = interpreter(&sh);
        assert!(
            loader.as_ref().is_some_and(|p| p.is_absolute()),
            "{loader:?}"
        );
    }
}
