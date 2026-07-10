//! Read APIs: file content and directory listings at a ref or commit.
//!
//! `GET /api/<repo>/file/<refish>/<path>` — raw blob bytes.
//! `GET /api/<repo>/tree/<refish>/<path>` — JSON listing with last-commit
//! attribution per entry (the "files in a directory" blame view), served
//! from the push-time file-log index — no history walk.

use crate::object::{ObjType, Oid};
use crate::odb::Odb;
use crate::refs::RepoState;
use crate::repo::{FileLogSegment, FileLogView};
use serde::Serialize;

/// Resolve a "refish" — a full hex oid, `HEAD`, a branch, or a tag — to a
/// commit oid.
pub async fn resolve_refish(state: &RepoState, odb: &Odb<'_>, refish: &str) -> Result<Oid, String> {
    if let Some(oid) = Oid::from_hex(refish) {
        return odb.peel_to_commit(oid).await;
    }
    let target = if refish == "HEAD" {
        state.head_oid()
    } else {
        state
            .refs
            .get(&format!("refs/heads/{refish}"))
            .or_else(|| state.refs.get(&format!("refs/tags/{refish}")))
            .or_else(|| state.refs.get(refish))
    };
    let hex = target.ok_or_else(|| format!("unknown ref {refish}"))?;
    let oid = Oid::from_hex(hex).ok_or("corrupt ref")?;
    odb.peel_to_commit(oid).await
}

/// Walk `path` from a commit's root tree. Returns `(mode, oid)` of the entry,
/// or the root tree itself for the empty path.
pub async fn resolve_path(
    odb: &Odb<'_>,
    commit: Oid,
    path: &str,
) -> Result<Option<(String, Oid)>, String> {
    let root = odb.read_commit(commit).await?.tree;
    if path.is_empty() {
        return Ok(Some(("40000".to_string(), root)));
    }
    let mut cursor = root;
    let components: Vec<&str> = path.split('/').filter(|c| !c.is_empty()).collect();
    for (i, comp) in components.iter().enumerate() {
        let entries = odb.read_tree(cursor).await?;
        match entries.iter().find(|e| e.name == *comp) {
            Some(e) if i == components.len() - 1 => return Ok(Some((e.mode.clone(), e.oid))),
            Some(e) if e.is_tree() => cursor = e.oid,
            _ => return Ok(None),
        }
    }
    Ok(None)
}

/// Fetch a file's raw contents at a commit.
pub async fn file_contents(
    odb: &Odb<'_>,
    commit: Oid,
    path: &str,
) -> Result<Option<Vec<u8>>, String> {
    match resolve_path(odb, commit, path).await? {
        Some((mode, oid)) if mode != "40000" && mode != "040000" => {
            let data = odb.read_typed(oid, ObjType::Blob).await?;
            Ok(Some((*data).clone()))
        }
        _ => Ok(None),
    }
}

/// One entry of a directory listing.
#[derive(Debug, Serialize)]
pub struct TreeEntryInfo {
    pub name: String,
    pub mode: String,
    /// "blob" or "tree".
    pub kind: &'static str,
    pub oid: String,
    /// Blob size (absent for trees).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub size: Option<u64>,
    /// Last commit that touched this entry (from the file-log index).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_commit: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_commit_time: Option<i64>,
}

/// List a directory at a commit, attributing each entry with the commit that
/// last touched it.
pub async fn list_tree(
    odb: &Odb<'_>,
    segments: &[FileLogSegment],
    commit: Oid,
    path: &str,
) -> Result<Option<Vec<TreeEntryInfo>>, String> {
    let tree = match resolve_path(odb, commit, path).await? {
        Some((mode, oid)) if mode == "40000" || mode == "040000" => oid,
        _ => return Ok(None),
    };
    let entries = odb.read_tree(tree).await?;
    // One pass over the file-log builds the lookup index; per-entry queries
    // are then O(log paths) instead of full scans.
    let view = FileLogView::new(segments);
    let mut out = Vec::with_capacity(entries.len());
    for e in entries.iter() {
        let full_path = if path.is_empty() {
            e.name.clone()
        } else {
            format!("{path}/{}", e.name)
        };
        let (kind, size, last) = if e.is_tree() {
            (
                "tree",
                None,
                view.latest_for_prefix(&format!("{full_path}/")),
            )
        } else {
            let size = odb.locate(e.oid).map(|(_, rec)| rec.size);
            ("blob", size, view.latest_for_path(&full_path))
        };
        out.push(TreeEntryInfo {
            name: e.name.clone(),
            mode: e.mode.clone(),
            kind,
            oid: e.oid.to_hex(),
            size,
            last_commit: last.map(|r| r.commit.clone()),
            last_commit_time: last.map(|r| r.time),
        });
    }
    Ok(Some(out))
}
