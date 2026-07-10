//! Git object model: ids, types, header hashing, and tree/commit parsing.
//!
//! This prototype targets SHA-1 repositories (git's default object format;
//! `object-format=sha1` is what stock clients negotiate). The [`Oid`] type is
//! a fixed 20-byte array so the hot paths (pack indexing, oid maps) never
//! allocate per id.

use sha1::{Digest, Sha1};

/// A SHA-1 object id.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Oid(pub [u8; 20]);

impl Oid {
    pub const ZERO: Oid = Oid([0u8; 20]);

    pub fn from_hex(s: &str) -> Option<Oid> {
        let bytes = hex::decode(s.trim()).ok()?;
        let arr: [u8; 20] = bytes.try_into().ok()?;
        Some(Oid(arr))
    }

    pub fn from_bytes(b: &[u8]) -> Option<Oid> {
        let arr: [u8; 20] = b.try_into().ok()?;
        Some(Oid(arr))
    }

    pub fn to_hex(&self) -> String {
        hex::encode(self.0)
    }

    pub fn is_zero(&self) -> bool {
        self.0 == [0u8; 20]
    }

    /// First byte, used for pack-index fan-out.
    pub fn first_byte(&self) -> u8 {
        self.0[0]
    }
}

impl std::fmt::Debug for Oid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Oid({})", self.to_hex())
    }
}

impl std::fmt::Display for Oid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_hex())
    }
}

/// The four first-class git object types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ObjType {
    Commit,
    Tree,
    Blob,
    Tag,
}

impl ObjType {
    pub fn name(&self) -> &'static str {
        match self {
            ObjType::Commit => "commit",
            ObjType::Tree => "tree",
            ObjType::Blob => "blob",
            ObjType::Tag => "tag",
        }
    }

    pub fn from_name(name: &str) -> Option<ObjType> {
        match name {
            "commit" => Some(ObjType::Commit),
            "tree" => Some(ObjType::Tree),
            "blob" => Some(ObjType::Blob),
            "tag" => Some(ObjType::Tag),
            _ => None,
        }
    }

    /// Pack entry type number (gitformat-pack(5)).
    pub fn pack_type(&self) -> u8 {
        match self {
            ObjType::Commit => 1,
            ObjType::Tree => 2,
            ObjType::Blob => 3,
            ObjType::Tag => 4,
        }
    }

    pub fn from_pack_type(t: u8) -> Option<ObjType> {
        match t {
            1 => Some(ObjType::Commit),
            2 => Some(ObjType::Tree),
            3 => Some(ObjType::Blob),
            4 => Some(ObjType::Tag),
            _ => None,
        }
    }
}

/// Hash an object's canonical form: `"<type> <size>\0" + content`.
pub fn hash_object(ty: ObjType, content: &[u8]) -> Oid {
    let mut h = Sha1::new();
    h.update(ty.name().as_bytes());
    h.update(b" ");
    h.update(content.len().to_string().as_bytes());
    h.update([0u8]);
    h.update(content);
    Oid(h.finalize().into())
}

/// Incremental object hasher for streaming paths where the content arrives in
/// chunks (the size must be known up front, which pack entries provide).
pub struct ObjectHasher {
    inner: Sha1,
}

impl ObjectHasher {
    pub fn new(ty: ObjType, size: u64) -> Self {
        let mut inner = Sha1::new();
        inner.update(ty.name().as_bytes());
        inner.update(b" ");
        inner.update(size.to_string().as_bytes());
        inner.update([0u8]);
        ObjectHasher { inner }
    }

    pub fn update(&mut self, chunk: &[u8]) {
        self.inner.update(chunk);
    }

    pub fn finish(self) -> Oid {
        Oid(self.inner.finalize().into())
    }
}

/// One entry in a tree object.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TreeEntry {
    /// Octal mode string as stored (e.g. "100644", "40000", "120000").
    pub mode: String,
    pub name: String,
    pub oid: Oid,
}

impl TreeEntry {
    pub fn is_tree(&self) -> bool {
        self.mode == "40000" || self.mode == "040000"
    }
}

/// Parse a tree object's content into entries.
///
/// Format: repeated `"<mode> <name>\0" + 20 raw oid bytes`.
pub fn parse_tree(content: &[u8]) -> Result<Vec<TreeEntry>, String> {
    let mut entries = Vec::new();
    let mut pos = 0;
    while pos < content.len() {
        let space = content[pos..]
            .iter()
            .position(|&b| b == b' ')
            .ok_or("tree entry: missing space")?
            + pos;
        let nul = content[space..]
            .iter()
            .position(|&b| b == 0)
            .ok_or("tree entry: missing NUL")?
            + space;
        if nul + 21 > content.len() {
            return Err("tree entry: truncated oid".into());
        }
        let mode = std::str::from_utf8(&content[pos..space])
            .map_err(|_| "tree entry: non-utf8 mode")?
            .to_string();
        let name = String::from_utf8_lossy(&content[space + 1..nul]).into_owned();
        let oid = Oid::from_bytes(&content[nul + 1..nul + 21]).unwrap();
        entries.push(TreeEntry { mode, name, oid });
        pos = nul + 21;
    }
    Ok(entries)
}

/// Serialize tree entries back to git's canonical tree format. Entries must
/// already be in git's tree sort order.
pub fn encode_tree(entries: &[TreeEntry]) -> Vec<u8> {
    let mut out = Vec::new();
    for e in entries {
        out.extend_from_slice(e.mode.as_bytes());
        out.push(b' ');
        out.extend_from_slice(e.name.as_bytes());
        out.push(0);
        out.extend_from_slice(&e.oid.0);
    }
    out
}

/// The parsed header of a commit object (message tail is kept raw).
#[derive(Debug, Clone)]
pub struct Commit {
    pub tree: Oid,
    pub parents: Vec<Oid>,
    /// Raw `author` line (name, email, timestamp, tz), unparsed.
    pub author: String,
    /// Raw `committer` line.
    pub committer: String,
    /// Commit timestamp (seconds since epoch) parsed from the committer line,
    /// 0 if unparseable. Used for ordering in the file-log index.
    pub commit_time: i64,
    pub message: String,
}

/// Parse a commit object's content.
pub fn parse_commit(content: &[u8]) -> Result<Commit, String> {
    let text = std::str::from_utf8(content).map_err(|_| "commit: non-utf8")?;
    let mut tree = None;
    let mut parents = Vec::new();
    let mut author = String::new();
    let mut committer = String::new();
    let mut lines = text.split('\n');
    for line in lines.by_ref() {
        if line.is_empty() {
            break; // header/message separator
        }
        if let Some(rest) = line.strip_prefix("tree ") {
            tree = Oid::from_hex(rest);
        } else if let Some(rest) = line.strip_prefix("parent ") {
            parents.push(Oid::from_hex(rest).ok_or("commit: bad parent oid")?);
        } else if let Some(rest) = line.strip_prefix("author ") {
            author = rest.to_string();
        } else if let Some(rest) = line.strip_prefix("committer ") {
            committer = rest.to_string();
        }
        // Other headers (gpgsig, encoding, mergetag …) are ignored here; the
        // raw object is always preserved byte-for-byte in the pack.
    }
    let message: String = lines.collect::<Vec<_>>().join("\n");
    let commit_time = parse_ident_time(&committer).unwrap_or(0);
    Ok(Commit {
        tree: tree.ok_or("commit: missing tree")?,
        parents,
        author,
        committer,
        commit_time,
        message,
    })
}

/// Extract the epoch-seconds timestamp from an ident line
/// (`Name <email> 1234567890 +0000`).
fn parse_ident_time(ident: &str) -> Option<i64> {
    let mut it = ident.rsplitn(3, ' ');
    let _tz = it.next()?;
    it.next()?.parse().ok()
}

/// A fully materialized object (type + raw content).
#[derive(Debug, Clone)]
pub struct Object {
    pub ty: ObjType,
    pub data: Vec<u8>,
}

impl Object {
    pub fn oid(&self) -> Oid {
        hash_object(self.ty, &self.data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_empty_blob_matches_git() {
        // `git hash-object -t blob /dev/null`
        assert_eq!(
            hash_object(ObjType::Blob, b"").to_hex(),
            "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
        );
    }

    #[test]
    fn hash_hello_blob_matches_git() {
        // `echo 'hello' | git hash-object --stdin`
        assert_eq!(
            hash_object(ObjType::Blob, b"hello\n").to_hex(),
            "ce013625030ba8dba906f756967f9e9ca394464a"
        );
    }

    #[test]
    fn streaming_hasher_matches_oneshot() {
        let data = b"some content that arrives in chunks";
        let mut h = ObjectHasher::new(ObjType::Blob, data.len() as u64);
        for c in data.chunks(7) {
            h.update(c);
        }
        assert_eq!(h.finish(), hash_object(ObjType::Blob, data));
    }

    #[test]
    fn tree_roundtrip() {
        let entries = vec![
            TreeEntry {
                mode: "100644".into(),
                name: "a.txt".into(),
                oid: hash_object(ObjType::Blob, b"a"),
            },
            TreeEntry {
                mode: "40000".into(),
                name: "dir".into(),
                oid: hash_object(ObjType::Tree, b""),
            },
        ];
        let enc = encode_tree(&entries);
        assert_eq!(parse_tree(&enc).unwrap(), entries);
    }

    #[test]
    fn commit_parse() {
        let content = b"tree 4b825dc642cb6eb9a060e54bf8d69288fbee4904\n\
parent ce013625030ba8dba906f756967f9e9ca394464a\n\
author A U Thor <a@example.com> 1700000000 +0000\n\
committer C O Mitter <c@example.com> 1700000001 +0100\n\
\n\
subject line\n\nbody\n";
        let c = parse_commit(content).unwrap();
        assert_eq!(c.tree.to_hex(), "4b825dc642cb6eb9a060e54bf8d69288fbee4904");
        assert_eq!(c.parents.len(), 1);
        assert_eq!(c.commit_time, 1700000001);
        assert!(c.message.starts_with("subject line"));
    }
}
