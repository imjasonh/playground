//! The FUSE filesystem: presents [`Source`] as
//!
//! ```text
//! /commits/<sha>/<path>   commit trees (immutable ⇒ long kernel TTLs)
//! /refs/<ref>             "<sha>\n" files (mutable ⇒ short TTLs, direct IO)
//! ```
//!
//! `/commits` itself lists nothing (the namespace is every commit sha), but
//! any existing commit resolves on lookup. `/refs` mirrors the ref namespace
//! with the `refs/` prefix stripped (`/refs/heads/main`, `/refs/tags/v1`)
//! plus `HEAD`.
//!
//! # Threading
//!
//! fuser dispatches requests on a single session thread. Every operation
//! that can block — a cache miss goes to the remote over HTTP — is bounced
//! to a small worker pool and answered asynchronously, so one slow read
//! never stalls the whole mount. This is also a correctness requirement:
//! when this process spawns a git child (fetch, cat-file), the child's
//! `execve` closes inherited FUSE-file descriptors, which makes the kernel
//! send FLUSH requests; those must be answerable while other operations are
//! in flight, or any same-process reader (like the e2e tests) deadlocks.
//! FLUSH itself is answered inline on the session thread.

use crate::source::{Entry, EntryKind, RefsSnapshot, Source};
use crate::vlog;
use fuser::{
    FileAttr, FileType, Filesystem, KernelConfig, ReplyAttr, ReplyData, ReplyDirectory,
    ReplyDirectoryPlus, ReplyEmpty, ReplyEntry, ReplyOpen, Request, FUSE_ROOT_ID,
};
use std::collections::HashMap;
use std::ffi::OsStr;
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime};

/// Commit-addressed data never changes; let the kernel cache it hard.
const IMMUTABLE_TTL: Duration = Duration::from_secs(3600);

/// A ref file's content: 40 hex chars + newline.
const REF_FILE_SIZE: u64 = 41;

/// Worker threads answering FUSE requests. Bounds how many slow remote
/// fetches can be in flight at once; everything above this queues.
const FS_WORKERS: usize = 8;

const INO_ROOT: u64 = FUSE_ROOT_ID; // 1
const INO_COMMITS: u64 = 2;
const INO_REFS: u64 = 3;
const FIRST_DYNAMIC_INO: u64 = 4;

#[derive(Debug, Clone)]
enum Node {
    Root,
    /// `/commits`.
    Commits,
    /// A path under `/refs`: `""` is `/refs` itself; otherwise a ref name
    /// with the `refs/` prefix stripped (`heads`, `heads/main`) or `HEAD`.
    /// Whether it is a file or directory depends on the current snapshot.
    Ref {
        rel: String,
    },
    /// `/commits/<sha>[/<path>]`. `entry` is `None` for the commit root
    /// (always a directory).
    Commit {
        commit: String,
        path: String,
        entry: Option<Entry>,
    },
}

/// One inode-table slot.
struct NodeSlot {
    node: Node,
    /// Canonical key for reverse-map cleanup; `None` for the static inos
    /// (root, `/commits`, `/refs`), which are never evicted.
    key: Option<String>,
    /// The kernel's lookup count for this inode: incremented once per
    /// LOOKUP reply and per delivered READDIRPLUS entry, decremented by
    /// FORGET. At zero the kernel holds no reference and the slot is
    /// evicted — this is what keeps the table from growing without bound
    /// on large traversals.
    nlookup: u64,
}

/// Inode table: ino → node, plus a canonical-key reverse map so re-lookups
/// reuse live inodes. Inos are never reused after eviction (a fresh one is
/// allocated from the monotonic counter), so the FUSE generation number can
/// stay 0.
struct NodeTable {
    nodes: HashMap<u64, NodeSlot>,
    ino_by_key: HashMap<String, u64>,
    next_ino: u64,
}

impl NodeTable {
    fn new() -> NodeTable {
        let mut nodes = HashMap::new();
        for (ino, node) in [
            (INO_ROOT, Node::Root),
            (INO_COMMITS, Node::Commits),
            (INO_REFS, Node::Ref { rel: String::new() }),
        ] {
            nodes.insert(
                ino,
                NodeSlot {
                    node,
                    key: None,
                    nlookup: 0,
                },
            );
        }
        NodeTable {
            nodes,
            ino_by_key: HashMap::new(),
            next_ino: FIRST_DYNAMIC_INO,
        }
    }

    /// Map a key to an inode without counting a kernel reference (used
    /// while building readdirplus replies; count only what gets
    /// delivered).
    fn intern(&mut self, key: String, node: Node) -> u64 {
        if let Some(&ino) = self.ino_by_key.get(&key) {
            // Refresh the stored node: for commit paths it's identical, for
            // ref paths the shape may have changed with the snapshot.
            self.nodes.get_mut(&ino).expect("slot for keyed ino").node = node;
            return ino;
        }
        let ino = self.next_ino;
        self.next_ino += 1;
        self.ino_by_key.insert(key.clone(), ino);
        self.nodes.insert(
            ino,
            NodeSlot {
                node,
                key: Some(key),
                nlookup: 0,
            },
        );
        ino
    }

    /// Record kernel references (LOOKUP replies / delivered readdirplus
    /// entries). Static inos are not refcounted.
    fn bump(&mut self, ino: u64, n: u64) {
        if let Some(slot) = self.nodes.get_mut(&ino) {
            if slot.key.is_some() {
                slot.nlookup += n;
            }
        }
    }

    /// FORGET from the kernel: drop references, evicting the slot when the
    /// count reaches zero.
    fn forget(&mut self, ino: u64, n: u64) {
        let Some(slot) = self.nodes.get_mut(&ino) else {
            return;
        };
        if slot.key.is_none() {
            return; // static inos live for the mount's lifetime
        }
        slot.nlookup = slot.nlookup.saturating_sub(n);
        if slot.nlookup == 0 {
            let key = slot.key.take();
            self.nodes.remove(&ino);
            if let Some(key) = key {
                self.ino_by_key.remove(&key);
            }
        }
    }

    fn get(&self, ino: u64) -> Option<Node> {
        self.nodes.get(&ino).map(|slot| slot.node.clone())
    }
}

/// A blob pinned for the lifetime of one open file: filled lazily by the
/// first read (so opens served from the kernel page cache never fetch) and
/// released on close. This is what makes files bigger than the LRU budget
/// read in one fetch instead of one fetch per 128 KiB read request.
type OpenBlob = Arc<Mutex<Option<Arc<Vec<u8>>>>>;

/// Everything the worker threads need, shared behind an `Arc`.
struct Inner {
    source: Source,
    refs_ttl: Duration,
    table: Mutex<NodeTable>,
    /// Open regular-file handles (fh → lazily-filled blob pin).
    handles: Mutex<HashMap<u64, OpenBlob>>,
    next_fh: std::sync::atomic::AtomicU64,
    uid: u32,
    gid: u32,
    mounted_at: SystemTime,
}

/// How a ref-namespace path resolves against a snapshot.
enum RefShape {
    File(String), // full ref name (or "HEAD") to resolve to an oid
    Dir,
    Missing,
}

/// One directory entry as resolved by [`Inner::dir_children`]: its name and
/// the node it would intern to.
struct DirChild {
    name: String,
    node: Node,
}

impl Inner {
    fn dir_attr(&self, ino: u64) -> FileAttr {
        self.attr(ino, FileType::Directory, 0, 0o555)
    }

    fn attr(&self, ino: u64, kind: FileType, size: u64, perm: u16) -> FileAttr {
        FileAttr {
            ino,
            size,
            blocks: size.div_ceil(512),
            atime: self.mounted_at,
            mtime: self.mounted_at,
            ctime: self.mounted_at,
            crtime: self.mounted_at,
            kind,
            perm,
            nlink: 1,
            uid: self.uid,
            gid: self.gid,
            rdev: 0,
            blksize: 4096,
            flags: 0,
        }
    }

    /// Classify `rel` (a path under `/refs`) against the current snapshot.
    fn ref_shape(snap: &RefsSnapshot, rel: &str) -> RefShape {
        if rel.is_empty() {
            return RefShape::Dir;
        }
        if rel == "HEAD" {
            // An unborn HEAD (empty repo, or symref to a deleted branch)
            // has no sha to expose; pretend it doesn't exist rather than
            // stat-ing a file whose read would fail.
            return if snap.refs.contains_key(&snap.head) {
                RefShape::File("HEAD".to_string())
            } else {
                RefShape::Missing
            };
        }
        let full = format!("refs/{rel}");
        if snap.refs.contains_key(&full) {
            return RefShape::File(full);
        }
        let prefix = format!("{full}/");
        if snap.refs.keys().any(|r| r.starts_with(&prefix)) {
            return RefShape::Dir;
        }
        RefShape::Missing
    }

    /// The `"<sha>\n"` content of a ref file.
    fn ref_content(snap: &RefsSnapshot, full_ref: &str) -> Option<Vec<u8>> {
        let oid = if full_ref == "HEAD" {
            snap.refs.get(&snap.head)?
        } else {
            snap.refs.get(full_ref)?
        };
        Some(format!("{oid}\n").into_bytes())
    }

    fn refs_snapshot(&self) -> Result<Arc<RefsSnapshot>, i32> {
        self.source.refs().map_err(|e| {
            vlog!("refs error: {e}");
            libc::EIO
        })
    }

    /// Attr for an entry under `/commits/<sha>/…`, resolving an unknown
    /// blob size by materializing the blob (rare).
    fn commit_attr(
        &self,
        ino: u64,
        commit: &str,
        path: &str,
        entry: Option<&Entry>,
    ) -> Result<FileAttr, i32> {
        match entry {
            None => Ok(self.dir_attr(ino)),
            Some(e) => match e.kind {
                EntryKind::Dir => Ok(self.dir_attr(ino)),
                EntryKind::File { exec } => {
                    let size = match e.size {
                        Some(s) => s,
                        None => self.resolve_size(ino, commit, path, &e.oid)?,
                    };
                    let perm = if exec { 0o555 } else { 0o444 };
                    Ok(self.attr(ino, FileType::RegularFile, size, perm))
                }
                EntryKind::Symlink => {
                    let size = match e.size {
                        Some(s) => s,
                        None => self.resolve_size(ino, commit, path, &e.oid)?,
                    };
                    Ok(self.attr(ino, FileType::Symlink, size, 0o777))
                }
            },
        }
    }

    fn resolve_size(&self, ino: u64, commit: &str, path: &str, oid: &str) -> Result<u64, i32> {
        let data = self
            .source
            .read_blob(commit, path, oid)
            .map_err(|_| libc::EIO)?;
        let size = data.len() as u64;
        // Remember it on the node so the next getattr is free.
        let mut table = self.table.lock().unwrap();
        if let Some(slot) = table.nodes.get_mut(&ino) {
            if let Node::Commit {
                entry: Some(entry), ..
            } = &mut slot.node
            {
                entry.size = Some(size);
            }
        }
        Ok(size)
    }

    /// Immediate children of a ref-namespace directory: subdirectory names
    /// and ref files, plus `HEAD` at the top level.
    fn ref_children(snap: &RefsSnapshot, rel: &str) -> Vec<(String, bool)> {
        let prefix = if rel.is_empty() {
            "refs/".to_string()
        } else {
            format!("refs/{rel}/")
        };
        let mut out: Vec<(String, bool)> = Vec::new();
        let mut seen = std::collections::BTreeMap::new();
        for name in snap.refs.keys() {
            let Some(rest) = name.strip_prefix(&prefix) else {
                continue;
            };
            match rest.split_once('/') {
                Some((first, _)) => {
                    seen.entry(first.to_string()).or_insert(true); // dir
                }
                None => {
                    seen.insert(rest.to_string(), false); // file
                }
            }
        }
        if rel.is_empty() && snap.refs.contains_key(&snap.head) {
            out.push(("HEAD".to_string(), false));
        }
        out.extend(seen);
        out
    }

    fn do_lookup(&self, parent: u64, name: &str, reply: ReplyEntry) {
        let Some(node) = self.table.lock().unwrap().get(parent) else {
            reply.error(libc::ENOENT);
            return;
        };
        match node {
            Node::Root => match name {
                "commits" => reply.entry(&IMMUTABLE_TTL, &self.dir_attr(INO_COMMITS), 0),
                "refs" => reply.entry(&self.refs_ttl, &self.dir_attr(INO_REFS), 0),
                _ => reply.error(libc::ENOENT),
            },
            Node::Commits => {
                let sha = name.to_ascii_lowercase();
                if sha.len() != 40 || !sha.bytes().all(|b| b.is_ascii_hexdigit()) {
                    reply.error(libc::ENOENT);
                    return;
                }
                match self.source.commit_exists(&sha) {
                    Ok(true) => {
                        let ino = {
                            let mut table = self.table.lock().unwrap();
                            let ino = table.intern(
                                format!("c:{sha}:"),
                                Node::Commit {
                                    commit: sha.clone(),
                                    path: String::new(),
                                    entry: None,
                                },
                            );
                            table.bump(ino, 1);
                            ino
                        };
                        reply.entry(&IMMUTABLE_TTL, &self.dir_attr(ino), 0);
                    }
                    Ok(false) => reply.error(libc::ENOENT),
                    Err(e) => {
                        vlog!("lookup commit {sha}: {e}");
                        reply.error(libc::EIO);
                    }
                }
            }
            Node::Ref { rel } => {
                let snap = match self.refs_snapshot() {
                    Ok(s) => s,
                    Err(errno) => {
                        reply.error(errno);
                        return;
                    }
                };
                let child = if rel.is_empty() {
                    name.to_string()
                } else {
                    format!("{rel}/{name}")
                };
                match Self::ref_shape(&snap, &child) {
                    RefShape::Missing => reply.error(libc::ENOENT),
                    shape => {
                        let ino = {
                            let mut table = self.table.lock().unwrap();
                            let ino = table
                                .intern(format!("r:{child}"), Node::Ref { rel: child.clone() });
                            table.bump(ino, 1);
                            ino
                        };
                        let attr = match shape {
                            RefShape::Dir => self.dir_attr(ino),
                            _ => self.attr(ino, FileType::RegularFile, REF_FILE_SIZE, 0o444),
                        };
                        reply.entry(&self.refs_ttl, &attr, 0);
                    }
                }
            }
            Node::Commit {
                commit,
                path,
                entry,
            } => {
                if entry.as_ref().is_some_and(|e| e.kind != EntryKind::Dir) {
                    reply.error(libc::ENOTDIR);
                    return;
                }
                match self.source.lookup(&commit, &path, name) {
                    Ok(Some(child)) => {
                        let child_path = if path.is_empty() {
                            name.to_string()
                        } else {
                            format!("{path}/{name}")
                        };
                        let ino = {
                            let mut table = self.table.lock().unwrap();
                            let ino = table.intern(
                                format!("c:{commit}:{child_path}"),
                                Node::Commit {
                                    commit: commit.clone(),
                                    path: child_path.clone(),
                                    entry: Some(child.clone()),
                                },
                            );
                            table.bump(ino, 1);
                            ino
                        };
                        match self.commit_attr(ino, &commit, &child_path, Some(&child)) {
                            Ok(attr) => reply.entry(&IMMUTABLE_TTL, &attr, 0),
                            Err(errno) => reply.error(errno),
                        }
                    }
                    Ok(None) => reply.error(libc::ENOENT),
                    Err(e) => {
                        vlog!("lookup {commit}:{path}/{name}: {e}");
                        reply.error(libc::EIO);
                    }
                }
            }
        }
    }

    fn do_getattr(&self, ino: u64, reply: ReplyAttr) {
        let Some(node) = self.table.lock().unwrap().get(ino) else {
            reply.error(libc::ENOENT);
            return;
        };
        match node {
            Node::Root | Node::Commits => reply.attr(&IMMUTABLE_TTL, &self.dir_attr(ino)),
            Node::Ref { rel } => {
                let snap = match self.refs_snapshot() {
                    Ok(s) => s,
                    Err(errno) => {
                        reply.error(errno);
                        return;
                    }
                };
                match Self::ref_shape(&snap, &rel) {
                    RefShape::Dir => reply.attr(&self.refs_ttl, &self.dir_attr(ino)),
                    RefShape::File(_) => reply.attr(
                        &self.refs_ttl,
                        &self.attr(ino, FileType::RegularFile, REF_FILE_SIZE, 0o444),
                    ),
                    RefShape::Missing => reply.error(libc::ENOENT),
                }
            }
            Node::Commit {
                commit,
                path,
                entry,
            } => match self.commit_attr(ino, &commit, &path, entry.as_ref()) {
                Ok(attr) => reply.attr(&IMMUTABLE_TTL, &attr),
                Err(errno) => reply.error(errno),
            },
        }
    }

    fn do_readlink(&self, ino: u64, reply: ReplyData) {
        let Some(Node::Commit {
            commit,
            path,
            entry: Some(entry),
        }) = self.table.lock().unwrap().get(ino)
        else {
            reply.error(libc::EINVAL);
            return;
        };
        if entry.kind != EntryKind::Symlink {
            reply.error(libc::EINVAL);
            return;
        }
        match self.source.read_blob(&commit, &path, &entry.oid) {
            Ok(data) => reply.data(&data),
            Err(e) => {
                vlog!("readlink {commit}:{path}: {e}");
                reply.error(libc::EIO);
            }
        }
    }

    /// The blob for a read on `fh`: served from the handle's pin when
    /// present, filling it on first use. `fh` 0 (or an unknown handle)
    /// falls back to an unpinned read.
    fn blob_for_read(
        &self,
        fh: u64,
        commit: &str,
        path: &str,
        oid: &str,
    ) -> Result<Arc<Vec<u8>>, String> {
        let slot = self.handles.lock().unwrap().get(&fh).cloned();
        match slot {
            Some(slot) => {
                let mut slot = slot.lock().unwrap();
                if let Some(data) = slot.as_ref() {
                    return Ok(data.clone());
                }
                let data = self.source.read_blob(commit, path, oid)?;
                *slot = Some(data.clone());
                Ok(data)
            }
            None => self.source.read_blob(commit, path, oid),
        }
    }

    fn do_read(&self, ino: u64, fh: u64, offset: i64, size: u32, reply: ReplyData) {
        let Some(node) = self.table.lock().unwrap().get(ino) else {
            reply.error(libc::ENOENT);
            return;
        };
        let data: Arc<Vec<u8>> = match node {
            Node::Ref { rel } => {
                let snap = match self.refs_snapshot() {
                    Ok(s) => s,
                    Err(errno) => {
                        reply.error(errno);
                        return;
                    }
                };
                match Self::ref_shape(&snap, &rel) {
                    RefShape::File(full) => match Self::ref_content(&snap, &full) {
                        Some(content) => Arc::new(content),
                        None => {
                            reply.error(libc::ENOENT);
                            return;
                        }
                    },
                    _ => {
                        reply.error(libc::EISDIR);
                        return;
                    }
                }
            }
            Node::Commit {
                commit,
                path,
                entry: Some(entry),
            } if entry.kind != EntryKind::Dir => {
                match self.blob_for_read(fh, &commit, &path, &entry.oid) {
                    Ok(data) => data,
                    Err(e) => {
                        vlog!("read {commit}:{path}: {e}");
                        reply.error(libc::EIO);
                        return;
                    }
                }
            }
            _ => {
                reply.error(libc::EISDIR);
                return;
            }
        };
        let start = (offset.max(0) as usize).min(data.len());
        let end = start.saturating_add(size as usize).min(data.len());
        reply.data(&data[start..end]);
    }

    /// The children of a directory node, or an errno. Shared by readdir and
    /// readdirplus. Each child comes with everything needed to intern its
    /// node and build its attr.
    fn dir_children(&self, node: &Node) -> Result<Vec<DirChild>, i32> {
        match node {
            Node::Root => Ok(vec![
                DirChild {
                    name: "commits".to_string(),
                    node: Node::Commits,
                },
                DirChild {
                    name: "refs".to_string(),
                    node: Node::Ref { rel: String::new() },
                },
            ]),
            // The commit namespace is every sha; list nothing.
            Node::Commits => Ok(Vec::new()),
            Node::Ref { rel } => {
                let snap = self.refs_snapshot()?;
                if !matches!(Self::ref_shape(&snap, rel), RefShape::Dir) {
                    return Err(libc::ENOTDIR);
                }
                Ok(Self::ref_children(&snap, rel)
                    .into_iter()
                    .map(|(name, _is_dir)| {
                        let child_rel = if rel.is_empty() {
                            name.clone()
                        } else {
                            format!("{rel}/{name}")
                        };
                        DirChild {
                            name,
                            node: Node::Ref { rel: child_rel },
                        }
                    })
                    .collect())
            }
            Node::Commit {
                commit,
                path,
                entry,
            } => {
                if entry.as_ref().is_some_and(|e| e.kind != EntryKind::Dir) {
                    return Err(libc::ENOTDIR);
                }
                match self.source.readdir(commit, path) {
                    Ok(Some(entries)) => Ok(entries
                        .into_iter()
                        .map(|e| {
                            let child_path = if path.is_empty() {
                                e.name.clone()
                            } else {
                                format!("{path}/{}", e.name)
                            };
                            DirChild {
                                name: e.name.clone(),
                                node: Node::Commit {
                                    commit: commit.clone(),
                                    path: child_path,
                                    entry: Some(e),
                                },
                            }
                        })
                        .collect()),
                    Ok(None) => Err(libc::ENOTDIR),
                    Err(e) => {
                        vlog!("readdir {commit}:{path}: {e}");
                        Err(libc::EIO)
                    }
                }
            }
        }
    }

    fn file_type_of(node: &Node, snap: Option<&RefsSnapshot>) -> FileType {
        match node {
            Node::Root | Node::Commits => FileType::Directory,
            Node::Ref { rel } => match snap.map(|s| Self::ref_shape(s, rel)) {
                Some(RefShape::File(_)) => FileType::RegularFile,
                _ => FileType::Directory,
            },
            Node::Commit { entry, .. } => match entry.as_ref().map(|e| e.kind) {
                None | Some(EntryKind::Dir) => FileType::Directory,
                Some(EntryKind::Symlink) => FileType::Symlink,
                Some(EntryKind::File { .. }) => FileType::RegularFile,
            },
        }
    }

    fn do_readdir(&self, ino: u64, offset: i64, mut reply: ReplyDirectory) {
        let Some(node) = self.table.lock().unwrap().get(ino) else {
            reply.error(libc::ENOENT);
            return;
        };
        let children = match self.dir_children(&node) {
            Ok(c) => c,
            Err(errno) => {
                reply.error(errno);
                return;
            }
        };
        // Ref-file vs ref-dir classification needs the snapshot; it is
        // already memoized from dir_children.
        let snap = self.source.refs().ok();
        // Directory stream: ".", "..", then children. `offset` is how many
        // entries the kernel already consumed. Inode numbers here are
        // advisory (plain readdir is not followed by inode-based access
        // without a lookup); lookup assigns the real ones.
        let mut stream: Vec<(FileType, String)> = Vec::with_capacity(children.len() + 2);
        stream.push((FileType::Directory, ".".to_string()));
        stream.push((FileType::Directory, "..".to_string()));
        for child in children {
            let ft = Self::file_type_of(&child.node, snap.as_deref());
            stream.push((ft, child.name));
        }
        for (i, (ft, name)) in stream.into_iter().enumerate().skip(offset.max(0) as usize) {
            if reply.add(ino, (i + 1) as i64, ft, &name) {
                break; // buffer full
            }
        }
        reply.ok();
    }

    /// READDIRPLUS: one reply carries names *and* attrs, so `ls -R`-style
    /// traversals skip a LOOKUP round trip per entry.
    fn do_readdirplus(&self, ino: u64, offset: i64, mut reply: ReplyDirectoryPlus) {
        let Some(node) = self.table.lock().unwrap().get(ino) else {
            reply.error(libc::ENOENT);
            return;
        };
        let children = match self.dir_children(&node) {
            Ok(c) => c,
            Err(errno) => {
                reply.error(errno);
                return;
            }
        };
        let dir_attr = self.dir_attr(ino);
        let ttl = match node {
            Node::Ref { .. } => self.refs_ttl,
            _ => IMMUTABLE_TTL,
        };
        // "." and ".." first (attrs of this dir are close enough for "..";
        // the kernel resolves both itself and ignores their lookup counts).
        let mut stream: Vec<(u64, FileAttr, String)> = Vec::with_capacity(children.len() + 2);
        stream.push((ino, dir_attr, ".".to_string()));
        stream.push((ino, dir_attr, "..".to_string()));
        for child in children {
            let child_ino = match &child.node {
                Node::Root => INO_ROOT,
                Node::Commits => INO_COMMITS,
                Node::Ref { rel } if rel.is_empty() => INO_REFS,
                Node::Ref { rel } => self
                    .table
                    .lock()
                    .unwrap()
                    .intern(format!("r:{rel}"), child.node.clone()),
                Node::Commit { commit, path, .. } => self
                    .table
                    .lock()
                    .unwrap()
                    .intern(format!("c:{commit}:{path}"), child.node.clone()),
            };
            let attr = match &child.node {
                Node::Root | Node::Commits => self.dir_attr(child_ino),
                Node::Ref { rel } => {
                    let snap = self.source.refs().ok();
                    match snap.as_deref().map(|s| Self::ref_shape(s, rel)) {
                        Some(RefShape::File(_)) => {
                            self.attr(child_ino, FileType::RegularFile, REF_FILE_SIZE, 0o444)
                        }
                        _ => self.dir_attr(child_ino),
                    }
                }
                Node::Commit {
                    commit,
                    path,
                    entry,
                } => match self.commit_attr(child_ino, commit, path, entry.as_ref()) {
                    Ok(a) => a,
                    Err(_) => continue, // skip unresolvable entries
                },
            };
            stream.push((child_ino, attr, child.name));
        }
        for (i, (entry_ino, attr, name)) in
            stream.into_iter().enumerate().skip(offset.max(0) as usize)
        {
            if reply.add(entry_ino, (i + 1) as i64, &name, &ttl, &attr, 0) {
                break; // buffer full; this entry was not delivered
            }
            // The kernel counts a lookup per delivered readdirplus entry —
            // except "." and ".." (the first two of the stream).
            if i >= 2 {
                self.table.lock().unwrap().bump(entry_ino, 1);
            }
        }
        reply.ok();
    }

    fn do_open(&self, ino: u64, flags: i32, reply: ReplyOpen) {
        if flags & libc::O_ACCMODE != libc::O_RDONLY {
            reply.error(libc::EROFS);
            return;
        }
        match self.table.lock().unwrap().get(ino) {
            // Ref files change under the kernel's feet; direct IO makes
            // every read hit us so `cat` always sees the current sha.
            Some(Node::Ref { .. }) => reply.opened(0, fuser::consts::FOPEN_DIRECT_IO),
            // Commit data is immutable; let the page cache keep it across
            // opens. Regular files get a handle that pins the blob for the
            // open's lifetime (filled lazily by the first read).
            Some(Node::Commit {
                entry: Some(entry), ..
            }) if entry.kind != EntryKind::Dir => {
                let fh = self
                    .next_fh
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                self.handles
                    .lock()
                    .unwrap()
                    .insert(fh, Arc::new(Mutex::new(None)));
                reply.opened(fh, fuser::consts::FOPEN_KEEP_CACHE);
            }
            Some(Node::Commit { .. }) => reply.opened(0, fuser::consts::FOPEN_KEEP_CACHE),
            Some(_) => reply.opened(0, 0),
            None => reply.error(libc::ENOENT),
        }
    }
}

/// A fixed pool of threads answering FUSE requests, fed by a channel.
struct WorkerPool {
    tx: std::sync::mpsc::Sender<Box<dyn FnOnce() + Send>>,
}

impl WorkerPool {
    fn new(size: usize) -> WorkerPool {
        let (tx, rx) = std::sync::mpsc::channel::<Box<dyn FnOnce() + Send>>();
        let rx = Arc::new(Mutex::new(rx));
        for i in 0..size {
            let rx = rx.clone();
            std::thread::Builder::new()
                .name(format!("git-fuse-fs-{i}"))
                .spawn(move || loop {
                    let job = rx.lock().unwrap().recv();
                    match job {
                        Ok(job) => job(),
                        Err(_) => return, // pool dropped
                    }
                })
                .expect("spawn fs worker");
        }
        WorkerPool { tx }
    }

    fn run(&self, job: impl FnOnce() + Send + 'static) {
        // Send only fails if all workers are gone, i.e. during teardown.
        let _ = self.tx.send(Box::new(job));
    }
}

pub(crate) struct GitFuse {
    inner: Arc<Inner>,
    pool: WorkerPool,
}

impl GitFuse {
    pub(crate) fn new(source: Source, refs_ttl: Duration) -> GitFuse {
        GitFuse {
            inner: Arc::new(Inner {
                source,
                refs_ttl,
                table: Mutex::new(NodeTable::new()),
                handles: Mutex::new(HashMap::new()),
                // fh 0 is reserved: "no handle" (ref files, directories).
                next_fh: std::sync::atomic::AtomicU64::new(1),
                // Present everything as owned by the mounting user.
                uid: unsafe { libc::geteuid() },
                gid: unsafe { libc::getegid() },
                mounted_at: SystemTime::now(),
            }),
            pool: WorkerPool::new(FS_WORKERS),
        }
    }
}

impl Filesystem for GitFuse {
    fn init(&mut self, _req: &Request<'_>, config: &mut KernelConfig) -> Result<(), libc::c_int> {
        // Best-effort: each capability is only added when the kernel offers
        // it. READDIRPLUS collapses readdir+lookup into one request;
        // PARALLEL_DIROPS lets concurrent traversals proceed in parallel;
        // CACHE_SYMLINKS keeps readlink results (immutable here) kernel-side.
        for cap in [
            fuser::consts::FUSE_DO_READDIRPLUS,
            fuser::consts::FUSE_READDIRPLUS_AUTO,
            fuser::consts::FUSE_PARALLEL_DIROPS,
            fuser::consts::FUSE_CACHE_SYMLINKS,
            // Lets read/readahead requests exceed the 32-page default —
            // fewer, larger reads for blob streaming.
            fuser::consts::FUSE_MAX_PAGES,
        ] {
            let _ = config.add_capabilities(cap);
        }
        let _ = config.set_max_readahead(1 << 20);
        Ok(())
    }

    fn lookup(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: ReplyEntry) {
        let Some(name) = name.to_str().map(str::to_string) else {
            reply.error(libc::ENOENT);
            return;
        };
        let inner = self.inner.clone();
        self.pool.run(move || inner.do_lookup(parent, &name, reply));
    }

    fn getattr(&mut self, _req: &Request<'_>, ino: u64, _fh: Option<u64>, reply: ReplyAttr) {
        let inner = self.inner.clone();
        self.pool.run(move || inner.do_getattr(ino, reply));
    }

    fn readlink(&mut self, _req: &Request<'_>, ino: u64, reply: ReplyData) {
        let inner = self.inner.clone();
        self.pool.run(move || inner.do_readlink(ino, reply));
    }

    fn open(&mut self, _req: &Request<'_>, ino: u64, flags: i32, reply: ReplyOpen) {
        let inner = self.inner.clone();
        self.pool.run(move || inner.do_open(ino, flags, reply));
    }

    fn read(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        fh: u64,
        offset: i64,
        size: u32,
        _flags: i32,
        _lock_owner: Option<u64>,
        reply: ReplyData,
    ) {
        let inner = self.inner.clone();
        self.pool
            .run(move || inner.do_read(ino, fh, offset, size, reply));
    }

    /// Inline on the session thread (a counter update): the kernel dropped
    /// references to an inode; evict it at zero so the table tracks what
    /// the kernel actually holds instead of growing forever.
    fn forget(&mut self, _req: &Request<'_>, ino: u64, nlookup: u64) {
        self.inner.table.lock().unwrap().forget(ino, nlookup);
    }

    /// Inline on the session thread (a map removal): drops the handle's
    /// blob pin.
    fn release(
        &mut self,
        _req: &Request<'_>,
        _ino: u64,
        fh: u64,
        _flags: i32,
        _lock_owner: Option<u64>,
        _flush: bool,
        reply: ReplyEmpty,
    ) {
        if fh != 0 {
            self.inner.handles.lock().unwrap().remove(&fh);
        }
        reply.ok();
    }

    fn readdir(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        _fh: u64,
        offset: i64,
        reply: ReplyDirectory,
    ) {
        let inner = self.inner.clone();
        self.pool.run(move || inner.do_readdir(ino, offset, reply));
    }

    fn readdirplus(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        _fh: u64,
        offset: i64,
        reply: ReplyDirectoryPlus,
    ) {
        let inner = self.inner.clone();
        self.pool
            .run(move || inner.do_readdirplus(ino, offset, reply));
    }

    /// Answered inline on the session thread: FLUSH arrives on *every*
    /// `close()` of an open file — including the implicit closes when a
    /// child of this very process calls `execve` — so it must never wait
    /// behind a slow remote read (see the module doc on threading).
    fn flush(
        &mut self,
        _req: &Request<'_>,
        _ino: u64,
        _fh: u64,
        _lock_owner: u64,
        reply: ReplyEmpty,
    ) {
        reply.ok();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn commit_node(path: &str) -> Node {
        Node::Commit {
            commit: "c".repeat(40),
            path: path.to_string(),
            entry: None,
        }
    }

    #[test]
    fn node_table_evicts_at_zero_and_never_reuses_inos() {
        let mut table = NodeTable::new();
        let a = table.intern("c:x:a".to_string(), commit_node("a"));
        table.bump(a, 2);
        assert!(table.get(a).is_some());

        // Same key → same ino while live.
        assert_eq!(table.intern("c:x:a".to_string(), commit_node("a")), a);

        table.forget(a, 1);
        assert!(table.get(a).is_some(), "one reference remains");
        table.forget(a, 1);
        assert!(table.get(a).is_none(), "evicted at zero");

        // Re-interning after eviction allocates a fresh ino (never reuse:
        // that's what lets the generation number stay 0).
        let a2 = table.intern("c:x:a".to_string(), commit_node("a"));
        assert_ne!(a2, a);
    }

    #[test]
    fn node_table_static_inos_are_immortal() {
        let mut table = NodeTable::new();
        table.forget(INO_ROOT, u64::MAX);
        table.forget(INO_COMMITS, u64::MAX);
        table.forget(INO_REFS, u64::MAX);
        assert!(table.get(INO_ROOT).is_some());
        assert!(table.get(INO_COMMITS).is_some());
        assert!(table.get(INO_REFS).is_some());
    }
}
