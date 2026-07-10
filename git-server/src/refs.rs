//! Repo state: refs, the pack manifest, and file-log segment list.
//!
//! All of a repository's *mutable* state lives in one small, versioned
//! document. In production it is owned by a per-repo Durable Object — the
//! single serialization point Cloudflare gives us — and updated with
//! optimistic concurrency (`commit` checks the expected version). Bulk data
//! never lives here; the document only *names* the immutable R2 objects that
//! hold it. That split is the core consistency story: a push becomes visible
//! atomically when this document flips, and readers always see a consistent
//! (refs, packs, filelog) snapshot.

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

/// Metadata for one stored pack.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PackMeta {
    /// Content id: hex of the pack's trailing SHA-1. Also its R2 key stem.
    pub id: String,
    /// Pack size in bytes (drives repack scheduling).
    pub bytes: u64,
    /// Number of objects.
    pub objects: u64,
}

/// The versioned per-repo state document.
#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
pub struct RepoState {
    /// Symref target of HEAD (e.g. "refs/heads/main").
    pub head: String,
    /// refname → hex oid.
    pub refs: BTreeMap<String, String>,
    /// Packs, oldest first. Later packs shadow earlier ones for reads.
    pub packs: Vec<PackMeta>,
    /// File-log segment ids, oldest first (parallel to pushes; merged by
    /// maintenance).
    pub filelog: Vec<String>,
}

impl RepoState {
    pub fn empty() -> Self {
        RepoState {
            head: "refs/heads/main".to_string(),
            ..Default::default()
        }
    }

    pub fn pack_ids(&self) -> Vec<String> {
        self.packs.iter().map(|p| p.id.clone()).collect()
    }

    /// The oid HEAD resolves to, if its target ref exists.
    pub fn head_oid(&self) -> Option<&String> {
        self.refs.get(&self.head)
    }
}

/// Errors from the state store.
#[derive(Debug, Clone)]
pub enum StateError {
    /// `commit` lost the race: someone else advanced the version.
    Conflict,
    Backend(String),
}

impl std::fmt::Display for StateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StateError::Conflict => write!(f, "state version conflict"),
            StateError::Backend(m) => write!(f, "state backend error: {m}"),
        }
    }
}

impl std::error::Error for StateError {}

/// The versioned state store (Durable Object in production).
#[async_trait(?Send)]
pub trait StateStore {
    /// Load a repo's state and its version. A repo that has never been pushed
    /// to returns `(RepoState::empty(), 0)`.
    async fn load(&self, repo: &str) -> Result<(RepoState, u64), StateError>;

    /// Atomically replace the state iff the stored version still equals
    /// `expected_version`. Returns the new version.
    async fn commit(
        &self,
        repo: &str,
        expected_version: u64,
        state: &RepoState,
    ) -> Result<u64, StateError>;
}

/// In-memory [`StateStore`] for tests/benchmarks. Cheap to clone and
/// thread-safe (see [`crate::storage::MemStore`]).
#[derive(Default, Clone)]
pub struct MemStateStore {
    inner: Arc<Mutex<BTreeMap<String, (RepoState, u64)>>>,
    /// Durable Object requests this store would have made in production
    /// (each `load` and `commit` is one DO request), for cost-model checks.
    ops: Arc<Mutex<u64>>,
}

impl MemStateStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn op_count(&self) -> u64 {
        *self.ops.lock().unwrap()
    }

    pub fn reset_op_count(&self) {
        *self.ops.lock().unwrap() = 0;
    }
}

#[async_trait(?Send)]
impl StateStore for MemStateStore {
    async fn load(&self, repo: &str) -> Result<(RepoState, u64), StateError> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::DoRequest);
        *self.ops.lock().unwrap() += 1;
        Ok(self
            .inner
            .lock()
            .unwrap()
            .get(repo)
            .cloned()
            .unwrap_or((RepoState::empty(), 0)))
    }

    async fn commit(
        &self,
        repo: &str,
        expected_version: u64,
        state: &RepoState,
    ) -> Result<u64, StateError> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::DoRequest);
        *self.ops.lock().unwrap() += 1;
        let mut map = self.inner.lock().unwrap();
        let current = map.get(repo).map(|(_, v)| *v).unwrap_or(0);
        if current != expected_version {
            return Err(StateError::Conflict);
        }
        let next = current + 1;
        map.insert(repo.to_string(), (state.clone(), next));
        Ok(next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::executor::block_on;

    #[test]
    fn cas_semantics() {
        block_on(async {
            let s = MemStateStore::new();
            let (state, v) = s.load("r").await.unwrap();
            assert_eq!(v, 0);
            assert!(state.refs.is_empty());

            let mut next = state.clone();
            next.refs.insert("refs/heads/main".into(), "a".repeat(40));
            let v1 = s.commit("r", v, &next).await.unwrap();
            assert_eq!(v1, 1);

            // Stale version loses.
            assert!(matches!(
                s.commit("r", 0, &next).await,
                Err(StateError::Conflict)
            ));

            let (loaded, v) = s.load("r").await.unwrap();
            assert_eq!(v, 1);
            assert_eq!(loaded.refs.len(), 1);
        });
    }
}
