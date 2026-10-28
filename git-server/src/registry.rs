//! The repo registry: which repos exist, for scheduled maintenance to walk.
//!
//! A push registers its repo (`register`) in a KV namespace so the nightly
//! cron (`#[event(scheduled)]` in `worker_entry.rs`) can find repos its own
//! per-push self-trigger wouldn't: a repo that stopped well below the
//! auto-repack pack-count trigger still leaves a few packs sitting
//! unconsolidated forever without something walking every registered name.
//!
//! KV's `list` is paginated: one call returns at most one page plus a cursor
//! for the rest, and a registry past that page size needs more calls to see
//! every name. [`list_all`] does that walk over the [`RepoRegistry`] trait,
//! so the paging logic runs under native `cargo test` even though the
//! production implementation (`worker_entry::KvRepoRegistry`) only builds
//! for `wasm32`.

use async_trait::async_trait;

/// One page of a [`list_all`] walk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegistryPage {
    /// Repo names in this page.
    pub names: Vec<String>,
    /// Pass to the next call's `cursor` to continue. Only meaningful when
    /// `complete` is `false`.
    pub cursor: Option<String>,
    /// `true` when this page was the registry's last.
    pub complete: bool,
}

/// Errors are stringly-typed like [`crate::storage::StorageError`]: a caller
/// can only log and let the next cron tick retry anyway.
pub type Result<T> = std::result::Result<T, String>;

/// The repo registry: a flat set of repo names, written on push and read by
/// scheduled maintenance. Backed by a KV namespace in production
/// (`worker_entry::KvRepoRegistry`); [`tests::FakeRegistry`] backs tests.
#[async_trait(?Send)]
pub trait RepoRegistry {
    /// Record `repo`, if it isn't already present.
    async fn register(&self, repo: &str) -> Result<()>;

    /// Fetch one page, continuing from `cursor` (the first page when
    /// `None`), the same shape KV's own `list` returns.
    async fn list_page(&self, cursor: Option<&str>) -> Result<RegistryPage>;
}

/// Walk every page of `registry`, following its cursor, and return every
/// registered name. A page reporting `complete: false` with no cursor stops
/// the walk instead of looping forever — defensive against a backend bug,
/// not a case any known implementation produces.
pub async fn list_all(registry: &dyn RepoRegistry) -> Result<Vec<String>> {
    let mut names = Vec::new();
    let mut cursor: Option<String> = None;
    loop {
        let page = registry.list_page(cursor.as_deref()).await?;
        names.extend(page.names);
        if page.complete {
            return Ok(names);
        }
        match page.cursor {
            Some(next) => cursor = Some(next),
            None => return Ok(names),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::executor::block_on;
    use std::cell::RefCell;

    /// A registry whose pages are pre-seeded in call order, so a test can
    /// assert `list_all` walks every one and stops exactly at `complete`.
    struct FakeRegistry {
        pages: RefCell<Vec<RegistryPage>>,
        seen_cursors: RefCell<Vec<Option<String>>>,
    }

    impl FakeRegistry {
        fn new(pages: Vec<RegistryPage>) -> Self {
            Self {
                pages: RefCell::new(pages),
                seen_cursors: RefCell::new(Vec::new()),
            }
        }
    }

    #[async_trait(?Send)]
    impl RepoRegistry for FakeRegistry {
        async fn register(&self, _repo: &str) -> Result<()> {
            unimplemented!("list_all tests don't register")
        }

        async fn list_page(&self, cursor: Option<&str>) -> Result<RegistryPage> {
            self.seen_cursors
                .borrow_mut()
                .push(cursor.map(String::from));
            let mut pages = self.pages.borrow_mut();
            if pages.is_empty() {
                return Err("list_page called past the last seeded page".into());
            }
            Ok(pages.remove(0))
        }
    }

    fn page(names: &[&str], cursor: Option<&str>, complete: bool) -> RegistryPage {
        RegistryPage {
            names: names.iter().map(|s| s.to_string()).collect(),
            cursor: cursor.map(String::from),
            complete,
        }
    }

    #[test]
    fn empty_registry_returns_no_names() {
        let registry = FakeRegistry::new(vec![page(&[], None, true)]);
        let names = block_on(list_all(&registry)).unwrap();
        assert!(names.is_empty());
    }

    #[test]
    fn single_page_stops_after_one_call() {
        let registry = FakeRegistry::new(vec![page(&["a", "b"], None, true)]);
        let names = block_on(list_all(&registry)).unwrap();
        assert_eq!(names, vec!["a", "b"]);
        assert_eq!(registry.seen_cursors.borrow().len(), 1);
    }

    /// The bug this module fixes: a registry bigger than one page must not
    /// be silently truncated to the first page.
    #[test]
    fn follows_cursor_across_multiple_pages() {
        let registry = FakeRegistry::new(vec![
            page(&["a", "b"], Some("cursor-1"), false),
            page(&["c"], Some("cursor-2"), false),
            page(&["d", "e"], None, true),
        ]);
        let names = block_on(list_all(&registry)).unwrap();
        assert_eq!(names, vec!["a", "b", "c", "d", "e"]);

        // Each call's cursor is the previous page's, and the first call has none.
        let seen = registry.seen_cursors.borrow();
        assert_eq!(
            *seen,
            vec![
                None,
                Some("cursor-1".to_string()),
                Some("cursor-2".to_string()),
            ]
        );
    }

    #[test]
    fn stops_if_incomplete_page_has_no_cursor() {
        // Defensive: a conforming backend never does this, but list_all must
        // not loop forever if one did.
        let registry = FakeRegistry::new(vec![page(&["a"], None, false)]);
        let names = block_on(list_all(&registry)).unwrap();
        assert_eq!(names, vec!["a"]);
    }

    #[test]
    fn propagates_page_error() {
        let registry = FakeRegistry::new(vec![page(&["a"], Some("cursor-1"), false)]);
        // Only one page seeded, so the second call (chasing cursor-1) errors.
        let err = block_on(list_all(&registry)).unwrap_err();
        assert!(err.contains("past the last seeded page"));
    }
}
