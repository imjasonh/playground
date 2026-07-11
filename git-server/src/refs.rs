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
    /// Packs/segments superseded by a repack swap but not yet deleted from
    /// storage (deferred deletion): an in-flight request that loaded the
    /// pre-swap manifest may still be reading them. A later repack run
    /// deletes entries older than its grace period and sweeps them from
    /// this list.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub retired: Vec<RetiredId>,
}

/// One deferred-deletion entry: a superseded pack/segment id and the swap
/// time that retired it.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RetiredId {
    pub id: String,
    pub ms: i64,
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

    /// Apply a repack's swap against the current state (pure — shared by the
    /// Durable Object and [`MemStateStore`]). Returns `false` (state
    /// untouched) if any consumed id is missing, which can only mean another
    /// repack raced this one: pushes append packs, they never remove them.
    ///
    /// The consolidated pack takes the position of the first removed pack,
    /// so the manifest's oldest-first shadowing order relative to packs
    /// outside the swap is preserved (the consolidation itself deduplicated
    /// oids keeping the newest copy within the consumed range). Consumed ids
    /// move to `retired` (deferred deletion — an in-flight reader may still
    /// hold the pre-swap manifest); ids in `sweep`, whose storage the caller
    /// already deleted after their grace period, leave `retired`.
    pub fn merge_repack(&mut self, swap: &RepackSwap) -> bool {
        let have_packs: std::collections::HashSet<&str> =
            self.packs.iter().map(|p| p.id.as_str()).collect();
        if !swap
            .remove_packs
            .iter()
            .all(|id| have_packs.contains(id.as_str()))
        {
            return false;
        }
        let have_filelog: std::collections::HashSet<&str> =
            self.filelog.iter().map(String::as_str).collect();
        if !swap
            .remove_filelog
            .iter()
            .all(|id| have_filelog.contains(id.as_str()))
        {
            return false;
        }

        if !swap.remove_packs.is_empty() {
            let new_pack = match &swap.new_pack {
                Some(p) => p,
                None => return false, // consolidation without a result pack
            };
            let removed: std::collections::HashSet<&str> =
                swap.remove_packs.iter().map(String::as_str).collect();
            let mut packs = Vec::with_capacity(self.packs.len() + 1 - swap.remove_packs.len());
            let mut inserted = false;
            for p in &self.packs {
                if removed.contains(p.id.as_str()) {
                    if !inserted {
                        packs.push(new_pack.clone());
                        inserted = true;
                    }
                } else {
                    packs.push(p.clone());
                }
            }
            self.packs = packs;

            let removed_fl: std::collections::HashSet<&str> =
                swap.remove_filelog.iter().map(String::as_str).collect();
            let mut filelog = Vec::with_capacity(self.filelog.len() + 1);
            let mut inserted_fl = false;
            for f in &self.filelog {
                if removed_fl.contains(f.as_str()) {
                    if !inserted_fl {
                        if let Some(new) = &swap.new_filelog {
                            filelog.push(new.clone());
                        }
                        inserted_fl = true;
                    }
                } else {
                    filelog.push(f.clone());
                }
            }
            self.filelog = filelog;

            // Retire the consumed ids (pack ids ∪ filelog ids — a push's
            // segment shares its pack's id, so dedupe).
            for id in swap.remove_packs.iter().chain(&swap.remove_filelog) {
                if !self.retired.iter().any(|r| &r.id == id) {
                    self.retired.push(RetiredId {
                        id: id.clone(),
                        ms: swap.now_ms,
                    });
                }
            }
        }

        if !swap.sweep.is_empty() {
            let swept: std::collections::HashSet<&str> =
                swap.sweep.iter().map(String::as_str).collect();
            self.retired.retain(|r| !swept.contains(r.id.as_str()));
        }
        true
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

/// One repack run's manifest change: replace a set of consumed pack ids
/// (and their file-log segment ids) with the consolidated pack, in place.
/// Applied via [`StateStore::apply_repack`], which — unlike a whole-document
/// CAS — **commutes with racing pushes**: a push only appends packs, so it
/// can never invalidate the swap. The swap fails only if a consumed id is
/// gone, i.e. another repack raced this one. Serializable: it crosses the
/// Durable Object boundary as JSON.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RepackSwap {
    /// Pack ids consumed by the consolidation (all must still be present).
    pub remove_packs: Vec<String>,
    /// The consolidated pack, inserted at the first removed pack's position
    /// so shadowing order relative to unselected packs is preserved.
    /// `None` for a sweep-only swap (no consolidation this run).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub new_pack: Option<PackMeta>,
    /// File-log segment ids consumed by the merge (all must be present).
    pub remove_filelog: Vec<String>,
    /// The merged segment id (`None` when the merge produced no records).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub new_filelog: Option<String>,
    /// Swap time (epoch ms): stamped on the retired ids for the deferred-
    /// deletion grace period.
    pub now_ms: i64,
    /// Retired ids whose grace period has expired and whose storage the
    /// caller has already deleted: drop them from `retired`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sweep: Vec<String>,
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

    /// Atomically apply a repack's swap ([`RepoState::merge_repack`]):
    /// replace the consumed pack/file-log ids with the consolidated ones,
    /// in place. Returns `Ok(false)` (state untouched) when a consumed id is
    /// gone — another repack raced. Racing *pushes* never conflict with
    /// this: they only append. Bumps the version when applied.
    async fn apply_repack(&self, repo: &str, swap: &RepackSwap) -> Result<bool, StateError>;
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

    async fn apply_repack(&self, repo: &str, swap: &RepackSwap) -> Result<bool, StateError> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::DoRequest);
        *self.ops.lock().unwrap() += 1;
        let mut map = self.inner.lock().unwrap();
        let (mut state, version) = map.get(repo).cloned().unwrap_or((RepoState::empty(), 0));
        let applied = state.merge_repack(swap);
        if applied {
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

    fn pack(id: &str) -> PackMeta {
        PackMeta {
            id: id.to_string(),
            bytes: 10,
            objects: 2,
        }
    }

    fn swap(
        remove: &[&str],
        new_pack: &str,
        remove_fl: &[&str],
        new_fl: Option<&str>,
    ) -> RepackSwap {
        RepackSwap {
            remove_packs: remove.iter().map(|s| s.to_string()).collect(),
            new_pack: Some(pack(new_pack)),
            remove_filelog: remove_fl.iter().map(|s| s.to_string()).collect(),
            new_filelog: new_fl.map(String::from),
            now_ms: 1000,
            sweep: Vec::new(),
        }
    }

    #[test]
    fn merge_repack_replaces_in_place_and_retires() {
        let mut state = RepoState::empty();
        state.packs = vec![pack("base"), pack("p1"), pack("p2"), pack("p3")];
        state.filelog = vec!["p1".into(), "p2".into(), "p3".into()];
        let ok = state.merge_repack(&swap(&["p1", "p2"], "m-1", &["p1", "p2"], Some("m-1")));
        assert!(ok);
        let ids: Vec<&str> = state.packs.iter().map(|p| p.id.as_str()).collect();
        assert_eq!(ids, vec!["base", "m-1", "p3"], "in-place, order preserved");
        assert_eq!(state.filelog, vec!["m-1".to_string(), "p3".to_string()]);
        // Consumed ids are retired (deduped: pack + segment share an id),
        // not gone from storage yet.
        let retired: Vec<&str> = state.retired.iter().map(|r| r.id.as_str()).collect();
        assert_eq!(retired, vec!["p1", "p2"]);
        assert!(state.retired.iter().all(|r| r.ms == 1000));
    }

    #[test]
    fn merge_repack_commutes_with_racing_push_appends() {
        // Repack planned against [p1, p2]; a push appends p3 before the swap
        // lands. The swap still applies; p3 is untouched.
        let mut state = RepoState::empty();
        state.packs = vec![pack("p1"), pack("p2")];
        state.merge_push(&PushDelta {
            ref_updates: vec![RefDelta {
                name: "refs/heads/x".into(),
                old: ZERO.into(),
                new: "a".repeat(40),
            }],
            new_pack: Some(pack("p3")),
            filelog: Some("p3".into()),
            last_push_ms: 1,
        });
        let ok = state.merge_repack(&swap(&["p1", "p2"], "m-1", &[], None));
        assert!(ok, "push appends never invalidate a repack swap");
        let ids: Vec<&str> = state.packs.iter().map(|p| p.id.as_str()).collect();
        assert_eq!(ids, vec!["m-1", "p3"]);
        assert_eq!(state.filelog, vec!["p3".to_string()]);
    }

    #[test]
    fn merge_repack_conflicts_when_a_consumed_pack_is_gone() {
        // A racing repack already consumed p1: the swap must not apply.
        let mut state = RepoState::empty();
        state.packs = vec![pack("m-other"), pack("p2")];
        state.filelog = vec!["p2".into()];
        let before = state.clone();
        let ok = state.merge_repack(&swap(&["p1", "p2"], "m-1", &[], None));
        assert!(!ok);
        assert_eq!(state, before, "state untouched on conflict");
    }

    #[test]
    fn merge_repack_sweep_clears_retired() {
        let mut state = RepoState::empty();
        state.packs = vec![pack("p1"), pack("p2"), pack("p3")];
        assert!(state.merge_repack(&swap(&["p1", "p2"], "m-1", &[], None)));
        assert_eq!(state.retired.len(), 2);
        // Next run: consolidates [m-1, p3] and sweeps the expired ids.
        let mut s2 = swap(&["m-1", "p3"], "m-2", &[], None);
        s2.sweep = vec!["p1".into(), "p2".into()];
        assert!(state.merge_repack(&s2));
        let retired: Vec<&str> = state.retired.iter().map(|r| r.id.as_str()).collect();
        assert_eq!(retired, vec!["m-1", "p3"], "old sweep out, new retire in");
        // Sweep-only swap (NoOp run with expired retired ids).
        let clear = RepackSwap {
            remove_packs: Vec::new(),
            new_pack: None,
            remove_filelog: Vec::new(),
            new_filelog: None,
            now_ms: 2000,
            sweep: vec!["m-1".into(), "p3".into()],
        };
        assert!(state.merge_repack(&clear));
        assert!(state.retired.is_empty());
        let ids: Vec<&str> = state.packs.iter().map(|p| p.id.as_str()).collect();
        assert_eq!(ids, vec!["m-2"]);
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
