//! Object filters for partial clone / partial fetch (`filter <spec>`).
//!
//! Specs follow `git rev-list --filter` / gitprotocol-v2(5). An object that
//! fails the filter is omitted from the pack **unless** it was named in an
//! explicit `want` line (so a follow-up blob fetch after `blob:none` works).

/// A parsed object filter. Currently: `blob:none`, `blob:limit=<n>`, and
/// `tree:<depth>` (the filters stock `git clone --filter=…` uses).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectFilter {
    /// Omit every blob.
    BlobNone,
    /// Omit blobs whose size is **≥** `limit` bytes.
    BlobLimit(u64),
    /// Omit trees (and their blobs) deeper than `depth`. Depth 0 keeps only
    /// commits/tags; depth 1 keeps root trees but no blobs or nested trees.
    TreeDepth(usize),
}

impl ObjectFilter {
    /// Parse a filter-spec string. Accepts scaled suffixes `k`/`m`/`g` on
    /// numeric limits (gitprotocol-v2 receivers SHOULD).
    pub fn parse(spec: &str) -> Result<ObjectFilter, String> {
        let spec = spec.trim();
        if spec == "blob:none" {
            return Ok(ObjectFilter::BlobNone);
        }
        if let Some(rest) = spec.strip_prefix("blob:limit=") {
            let limit =
                parse_scaled_size(rest).ok_or_else(|| format!("bad blob:limit value: {rest}"))?;
            return Ok(ObjectFilter::BlobLimit(limit));
        }
        if let Some(rest) = spec.strip_prefix("tree:") {
            let depth: usize = rest
                .parse()
                .map_err(|_| format!("bad tree filter depth: {rest}"))?;
            return Ok(ObjectFilter::TreeDepth(depth));
        }
        Err(format!("unsupported filter-spec: {spec}"))
    }

    /// Whether a tree entry at `tree_depth` (0 = root tree) should be walked
    /// into / included. `tree_depth` is the depth of the *parent tree* being
    /// walked (root = 0).
    pub fn include_tree_at(&self, tree_depth: usize) -> bool {
        match self {
            ObjectFilter::TreeDepth(max) => tree_depth < *max,
            _ => true,
        }
    }

    /// Whether a blob (or symlink blob) of `size` bytes should be included
    /// when discovered via a tree walk. Explicit `want`s bypass this.
    pub fn include_blob(&self, size: u64) -> bool {
        match self {
            ObjectFilter::BlobNone => false,
            ObjectFilter::BlobLimit(limit) => size < *limit,
            // tree:<depth> never ships blobs reached through trees that were
            // themselves included: blobs live at the next depth past a tree.
            // Callers only ask about blobs for entries under an included tree;
            // tree:N still omits those blobs (matching git's tree:N filter).
            ObjectFilter::TreeDepth(_) => false,
        }
    }
}

/// Parse a decimal size with optional `k`/`m`/`g` suffix (1024-based).
fn parse_scaled_size(s: &str) -> Option<u64> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    let (num, scale) = match s.as_bytes().last().map(u8::to_ascii_lowercase) {
        Some(b'k') => (&s[..s.len() - 1], 1024u64),
        Some(b'm') => (&s[..s.len() - 1], 1024 * 1024),
        Some(b'g') => (&s[..s.len() - 1], 1024 * 1024 * 1024),
        _ => (s, 1u64),
    };
    if num.is_empty() {
        return None;
    }
    let n: u64 = num.parse().ok()?;
    n.checked_mul(scale)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_blob_none() {
        assert_eq!(
            ObjectFilter::parse("blob:none").unwrap(),
            ObjectFilter::BlobNone
        );
        assert_eq!(
            ObjectFilter::parse("  blob:none  ").unwrap(),
            ObjectFilter::BlobNone
        );
    }

    #[test]
    fn parse_blob_limit_scaled() {
        assert_eq!(
            ObjectFilter::parse("blob:limit=1024").unwrap(),
            ObjectFilter::BlobLimit(1024)
        );
        assert_eq!(
            ObjectFilter::parse("blob:limit=1k").unwrap(),
            ObjectFilter::BlobLimit(1024)
        );
        assert_eq!(
            ObjectFilter::parse("blob:limit=2m").unwrap(),
            ObjectFilter::BlobLimit(2 * 1024 * 1024)
        );
        assert_eq!(
            ObjectFilter::parse("blob:limit=1g").unwrap(),
            ObjectFilter::BlobLimit(1024 * 1024 * 1024)
        );
        assert_eq!(
            ObjectFilter::parse("blob:limit=0").unwrap(),
            ObjectFilter::BlobLimit(0)
        );
    }

    #[test]
    fn parse_tree_depth() {
        assert_eq!(
            ObjectFilter::parse("tree:0").unwrap(),
            ObjectFilter::TreeDepth(0)
        );
        assert_eq!(
            ObjectFilter::parse("tree:2").unwrap(),
            ObjectFilter::TreeDepth(2)
        );
    }

    #[test]
    fn parse_rejects_unknown() {
        assert!(ObjectFilter::parse("sparse:oid=abc").is_err());
        assert!(ObjectFilter::parse("blob:limit=").is_err());
        assert!(ObjectFilter::parse("blob:limit=xk").is_err());
        assert!(ObjectFilter::parse("tree:x").is_err());
    }

    #[test]
    fn blob_none_omits_blobs_keeps_trees() {
        let f = ObjectFilter::BlobNone;
        assert!(!f.include_blob(0));
        assert!(!f.include_blob(1_000_000));
        assert!(f.include_tree_at(0));
        assert!(f.include_tree_at(99));
    }

    #[test]
    fn blob_limit_threshold() {
        let f = ObjectFilter::BlobLimit(100);
        assert!(f.include_blob(99));
        assert!(!f.include_blob(100));
        assert!(!f.include_blob(101));
    }

    #[test]
    fn tree_depth_bounds() {
        let f = ObjectFilter::TreeDepth(1);
        assert!(f.include_tree_at(0)); // root tree
        assert!(!f.include_tree_at(1)); // nested
        assert!(!f.include_blob(1));
    }
}
