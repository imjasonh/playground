//! Line-level blame, powered by the push-time file-log index.
//!
//! The classic blame algorithm walks the whole commit graph diffing trees to
//! find when a path changed — unaffordable in a Worker. Instead, every push
//! records, per changed path, a link to the *previous* (commit, blob) that
//! touched that path (see [`crate::repo::FileLogRecord`]). Blame then:
//!
//! 1. hops that chain to enumerate the file's versions, newest → oldest
//!    (one small index lookup, zero history walking);
//! 2. reads only the blob versions of *this file* from the odb;
//! 3. diffs each adjacent pair ([`crate::diff`]), attributing lines to the
//!    version where they first appear.
//!
//! Cost is proportional to the file's own change count, not repo history.
//!
//! Known approximation (documented in docs/design.md): the chain follows the
//! first-parent line as recorded at push time. Histories with concurrent
//! branches touching the same path can attribute a line to the merge-side
//! commit rather than the original author, like `git blame --first-parent`.

use crate::diff::{match_lines, split_lines};
use crate::object::{ObjType, Oid};
use crate::odb::Odb;
use crate::repo::{Change, FileLogSegment};
use serde::Serialize;

/// Attribution for one line of the blamed file.
#[derive(Debug, Clone, Serialize)]
pub struct BlameLine {
    /// 1-based line number in the blamed version.
    pub line: usize,
    /// Hex oid of the commit that introduced this line.
    pub commit: String,
    /// Commit time of that commit.
    pub time: i64,
}

/// A version of the file along its change chain.
struct Version {
    commit: String,
    time: i64,
    blob: Oid,
}

/// Compute blame for `path` as of `at_commit`.
///
/// Returns `None` if the path has no file-log chain (never touched) or does
/// not exist at that commit.
pub async fn blame(
    odb: &Odb<'_>,
    segments: &[FileLogSegment],
    at_commit: Oid,
    path: &str,
) -> Result<Option<Vec<BlameLine>>, String> {
    // Find the newest record for the path at-or-before `at_commit`. If the
    // requested commit itself touched the path there is an exact record;
    // otherwise the newest record is the right starting point for a tip
    // commit (see module docs for the branching caveat).
    let at_hex = at_commit.to_hex();
    let mut start: Option<&crate::repo::FileLogRecord> = None;
    'outer: for seg in segments {
        for r in seg.records.iter().rev() {
            if r.path == path && (start.is_none() || r.commit == at_hex) {
                start = Some(r);
                if r.commit == at_hex {
                    break 'outer;
                }
            }
        }
    }
    let start = match start {
        Some(r) => r,
        None => return Ok(None),
    };
    if start.change == Change::Delete {
        return Ok(None);
    }

    // Build the version chain, newest first, stopping at the introducing Add.
    let mut versions: Vec<Version> = Vec::new();
    let mut cursor = Some(start);
    while let Some(rec) = cursor {
        if rec.change == Change::Delete {
            // A delete inside the chain: everything newer was a re-add;
            // attribution stops at the re-add.
            break;
        }
        versions.push(Version {
            commit: rec.commit.clone(),
            time: rec.time,
            blob: Oid::from_hex(&rec.blob).ok_or("corrupt filelog blob oid")?,
        });
        if rec.change == Change::Add {
            break;
        }
        cursor = match (&rec.prev_commit, &rec.prev_blob) {
            (Some(pc), Some(_)) => find_record(segments, path, pc),
            _ => None,
        };
    }
    if versions.is_empty() {
        return Ok(None);
    }

    // Read the newest version's content; every line starts unattributed.
    let newest = odb.read_typed(versions[0].blob, ObjType::Blob).await?;
    let line_count = split_lines(&newest).len();
    let mut attribution: Vec<Option<usize>> = vec![None; line_count]; // version idx

    // `carry[i]` = which line of the *current* (older) version corresponds to
    // final line i, or None once attributed/lost.
    let mut carry: Vec<Option<usize>> = (0..line_count).map(Some).collect();
    let mut newer_content = newest;

    for vi in 0..versions.len() {
        let is_last = vi + 1 == versions.len();
        if is_last {
            // Introducing version: everything still unattributed belongs here.
            for (i, slot) in carry.iter().enumerate() {
                if slot.is_some() && attribution[i].is_none() {
                    attribution[i] = Some(vi);
                }
            }
            break;
        }
        let older_content = odb.read_typed(versions[vi + 1].blob, ObjType::Blob).await?;
        // matches: (older_line, newer_line) pairs.
        let matches = match_lines(&older_content, &newer_content);
        let mut newer_to_older: std::collections::HashMap<usize, usize> =
            std::collections::HashMap::with_capacity(matches.len());
        for (o, n) in matches {
            newer_to_older.insert(n, o);
        }
        for i in 0..line_count {
            if attribution[i].is_some() {
                continue;
            }
            if let Some(cur_line) = carry[i] {
                match newer_to_older.get(&cur_line) {
                    Some(&older_line) => carry[i] = Some(older_line),
                    None => {
                        // Line does not exist in the older version: it was
                        // introduced by this (newer) version.
                        attribution[i] = Some(vi);
                        carry[i] = None;
                    }
                }
            }
        }
        newer_content = older_content;
    }

    let out = attribution
        .iter()
        .enumerate()
        .map(|(i, a)| {
            let v = &versions[a.unwrap_or(0)];
            BlameLine {
                line: i + 1,
                commit: v.commit.clone(),
                time: v.time,
            }
        })
        .collect();
    Ok(Some(out))
}

fn find_record<'a>(
    segments: &'a [FileLogSegment],
    path: &str,
    commit_hex: &str,
) -> Option<&'a crate::repo::FileLogRecord> {
    for seg in segments {
        for r in seg.records.iter().rev() {
            if r.path == path && r.commit == commit_hex {
                return Some(r);
            }
        }
    }
    None
}
