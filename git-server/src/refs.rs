//! Repo state: refs, the pack manifest, and file-log segment list.
//!
//! All of a repository's *mutable* state lives in one small, versioned
//! document. In production it is owned by a per-repo Durable Object — the
//! single serialization point Cloudflare gives us. Bulk data never lives
//! here; the document only *names* the immutable R2 objects that hold it.
//! That split is the core consistency story: a push becomes visible
//! atomically when this document flips, and readers always see a consistent
//! (refs, packs, filelog) snapshot.
//!
//! Two write paths, with different concurrency rules:
//!
//! * **Pushes** send a [`PushDelta`] applied via [`StateStore::apply_push`]:
//!   per-ref old-value CAS (git's actual contract) plus commuting appends
//!   (pack, filelog segment). Concurrent pushes to *disjoint* refs both land;
//!   only a true same-ref race fails, per-ref, with `fetch first`. This is
//!   what lifts the per-repo write ceiling measured in
//!   `docs/loadtest-scaling.md` — the old whole-document CAS made the entire
//!   multi-second push pipeline one conflict window.
//! * **Maintenance (repack)** rewrites the pack list wholesale, so it keeps
//!   whole-document optimistic concurrency (`commit` checks the expected
//!   version). Every applied push bumps the version, so a repack racing any
//!   push loses and discards its staged output.

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
    /// Wall-clock time (epoch ms) of the last accepted push, recorded at
    /// apply time (the caller supplies the clock, since this crate is
    /// runtime-agnostic). `None` for a repo never pushed to. Surfaced by the
    /// status API as `last_push`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_push_ms: Option<i64>,
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

    /// Apply one push's delta against the *current* state (the merge-apply
    /// write path — see the module docs). Pure so the Durable Object and
    /// [`MemStateStore`] share one implementation.
    ///
    /// Per ref, in order: succeeds iff the ref's current value equals the
    /// claimed `old` (missing ref ≡ all-zeros), else fails with
    /// `fetch first`. If at least one ref landed: append the pack and
    /// file-log segment (idempotently, so a retried delta can't
    /// double-append), re-point HEAD if its target vanished, and stamp
    /// `last_push_ms`. If nothing landed the state is untouched and the
    /// staged pack becomes an orphan for the sweep.
    pub fn merge_push(&mut self, delta: &PushDelta) -> PushApplied {
        const ZERO: &str = "0000000000000000000000000000000000000000";
        let mut results = Vec::with_capacity(delta.ref_updates.len());
        let mut any_ok = false;
        for u in &delta.ref_updates {
            let current = self.refs.get(&u.name).map(String::as_str).unwrap_or(ZERO);
            if current != u.old {
                results.push(Some("fetch first".to_string()));
                continue;
            }
            if u.new == ZERO {
                self.refs.remove(&u.name);
            } else {
                self.refs.insert(u.name.clone(), u.new.clone());
            }
            results.push(None);
            any_ok = true;
        }
        if !any_ok {
            return PushApplied {
                results,
                applied: false,
            };
        }

        // Keep HEAD pointing at a branch that exists: fall back to `main`,
        // then the first branch.
        if !self.refs.contains_key(&self.head) {
            if self.refs.contains_key("refs/heads/main") {
                self.head = "refs/heads/main".to_string();
            } else if let Some(first) = self.refs.keys().find(|r| r.starts_with("refs/heads/")) {
                self.head = first.clone();
            }
        }

        if let Some(pack) = &delta.new_pack {
            if !self.packs.iter().any(|p| p.id == pack.id) {
                self.packs.push(pack.clone());
            }
        }
        if let Some(seg) = &delta.filelog {
            if !self.filelog.contains(seg) {
                self.filelog.push(seg.clone());
            }
        }
        self.last_push_ms = Some(delta.last_push_ms);
        PushApplied {
            results,
            applied: true,
        }
    }
}

/// One ref update inside a [`PushDelta`]: hex oids, all-zeros meaning
/// "absent" (`old`) / "delete" (`new`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RefDelta {
    pub name: String,
    pub old: String,
    pub new: String,
}

/// Everything one push changes, expressed as a delta so the state store can
/// merge it against the current state instead of replacing the whole
/// document. Serializable: it crosses the Durable Object boundary as JSON.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PushDelta {
    pub ref_updates: Vec<RefDelta>,
    /// The push's pack, already uploaded and indexed (append-only).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub new_pack: Option<PackMeta>,
    /// The push's file-log segment id, already written (append-only).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub filelog: Option<String>,
    /// Wall-clock time (epoch ms) stamped as the accepted-push time.
    pub last_push_ms: i64,
}

/// Result of [`StateStore::apply_push`].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PushApplied {
    /// Per-ref outcome, parallel to `PushDelta::ref_updates`; `None` = the
    /// update landed, `Some(reason)` = rejected (e.g. `fetch first`).
    pub results: Vec<Option<String>>,
    /// True iff at least one ref landed and the state was persisted.
    pub applied: bool,
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
    /// `expected_version`. Returns the new version. Used by maintenance
    /// (repack), which rewrites the pack list wholesale and must lose to any
    /// racing push.
    async fn commit(
        &self,
        repo: &str,
        expected_version: u64,
        state: &RepoState,
    ) -> Result<u64, StateError>;

    /// Atomically merge one push's delta against the *current* state
    /// ([`RepoState::merge_push`]): per-ref old-value CAS plus commuting
    /// appends. Bumps the version when applied, so racing `commit` callers
    /// (repack) observe the change.
    async fn apply_push(&self, repo: &str, delta: &PushDelta) -> Result<PushApplied, StateError>;
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

    async fn apply_push(&self, repo: &str, delta: &PushDelta) -> Result<PushApplied, StateError> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::DoRequest);
        *self.ops.lock().unwrap() += 1;
        let mut map = self.inner.lock().unwrap();
        let (mut state, version) = map.get(repo).cloned().unwrap_or((RepoState::empty(), 0));
        let applied = state.merge_push(delta);
        if applied.applied {
            map.insert(repo.to_string(), (state, version + 1));
        }
        Ok(applied)
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

    const ZERO: &str = "0000000000000000000000000000000000000000";

    fn delta(updates: &[(&str, &str, &str)]) -> PushDelta {
        PushDelta {
            ref_updates: updates
                .iter()
                .map(|(name, old, new)| RefDelta {
                    name: name.to_string(),
                    old: old.to_string(),
                    new: new.to_string(),
                })
                .collect(),
            new_pack: None,
            filelog: None,
            last_push_ms: 42,
        }
    }

    #[test]
    fn merge_push_disjoint_refs_both_land() {
        let a = "a".repeat(40);
        let b = "b".repeat(40);
        // Two pushes prepared against the same (empty) snapshot: under
        // whole-document CAS the second would conflict; merged per-ref,
        // both land.
        let mut state = RepoState::empty();
        let r1 = state.merge_push(&delta(&[("refs/heads/one", ZERO, &a)]));
        let r2 = state.merge_push(&delta(&[("refs/heads/two", ZERO, &b)]));
        assert!(r1.applied && r2.applied);
        assert_eq!(r1.results, vec![None]);
        assert_eq!(r2.results, vec![None]);
        assert_eq!(state.refs.len(), 2);
        assert_eq!(state.last_push_ms, Some(42));
    }

    #[test]
    fn merge_push_same_ref_race_loser_fails_per_ref() {
        let a = "a".repeat(40);
        let b = "b".repeat(40);
        let c = "c".repeat(40);
        let mut state = RepoState::empty();
        state.merge_push(&delta(&[("refs/heads/main", ZERO, &a)]));
        // A racing push prepared against the pre-`a` snapshot: its stale
        // main update fails, but the branch update in the same push lands.
        let out = state.merge_push(&delta(&[
            ("refs/heads/main", ZERO, &b),
            ("refs/heads/feature", ZERO, &c),
        ]));
        assert!(out.applied);
        assert_eq!(out.results[0].as_deref(), Some("fetch first"));
        assert_eq!(out.results[1], None);
        assert_eq!(state.refs["refs/heads/main"], a);
        assert_eq!(state.refs["refs/heads/feature"], c);
    }

    #[test]
    fn merge_push_all_stale_leaves_state_untouched() {
        let a = "a".repeat(40);
        let b = "b".repeat(40);
        let mut state = RepoState::empty();
        state.merge_push(&delta(&[("refs/heads/main", ZERO, &a)]));
        let before = state.clone();
        let mut d = delta(&[("refs/heads/main", &b, &a)]);
        d.new_pack = Some(PackMeta {
            id: "p-x".into(),
            bytes: 1,
            objects: 1,
        });
        let out = state.merge_push(&d);
        assert!(!out.applied);
        assert_eq!(state, before, "no pack/filelog append, no timestamp");
    }

    #[test]
    fn merge_push_delete_and_head_fallback() {
        let a = "a".repeat(40);
        let mut state = RepoState::empty();
        state.merge_push(&delta(&[("refs/heads/dev", ZERO, &a)]));
        assert_eq!(state.head, "refs/heads/dev", "fallback picked first branch");
        state.merge_push(&delta(&[("refs/heads/main", ZERO, &a)]));
        let out = state.merge_push(&delta(&[("refs/heads/dev", &a, ZERO)]));
        assert!(out.applied);
        assert!(!state.refs.contains_key("refs/heads/dev"));
        assert_eq!(state.head, "refs/heads/main");
    }

    #[test]
    fn merge_push_retry_is_idempotent() {
        let a = "a".repeat(40);
        let mut d = delta(&[("refs/heads/main", ZERO, &a)]);
        d.new_pack = Some(PackMeta {
            id: "p-1".into(),
            bytes: 10,
            objects: 2,
        });
        d.filelog = Some("p-1".into());
        let mut state = RepoState::empty();
        assert!(state.merge_push(&d).applied);
        // A retried delta (dropped response) must not double-append; the
        // ref update itself reports `fetch first` (old no longer matches)
        // but pack/filelog stay single.
        state.merge_push(&d);
        assert_eq!(state.packs.len(), 1);
        assert_eq!(state.filelog.len(), 1);
    }

    #[test]
    fn apply_push_bumps_version_for_repack_cas() {
        block_on(async {
            let s = MemStateStore::new();
            let (state, v0) = s.load("r").await.unwrap();
            let out = s
                .apply_push("r", &delta(&[("refs/heads/main", ZERO, &"a".repeat(40))]))
                .await
                .unwrap();
            assert!(out.applied);
            // A repack that loaded before the push must lose its CAS.
            assert!(matches!(
                s.commit("r", v0, &state).await,
                Err(StateError::Conflict)
            ));
            let (_, v1) = s.load("r").await.unwrap();
            assert_eq!(v1, v0 + 1);
        });
    }
}
