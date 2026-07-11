//! A tiny flush-on-budget object cache shared by the read paths.
//!
//! Both the odb (fetch/tree-walk reads) and push-time delta resolution keep
//! materialized objects around because access is clustered: delta bases sit
//! near their deltas, and tree walks revisit hot objects. One policy serves
//! both.

use crate::object::ObjType;
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;

/// A materialized object: type + shared content.
pub type CachedObject = (ObjType, Rc<Vec<u8>>);

/// Byte-budgeted object cache with whole-cache eviction: when an insert
/// would exceed the budget, everything is dropped. Crude but bounded — the
/// clustered access patterns rebuild the working set quickly after a flush,
/// and the policy needs no per-entry bookkeeping.
pub struct ByteBudgetCache<K> {
    map: HashMap<K, CachedObject>,
    bytes: usize,
    budget: usize,
}

impl<K: Eq + Hash> ByteBudgetCache<K> {
    pub fn new(budget: usize) -> Self {
        ByteBudgetCache {
            map: HashMap::new(),
            bytes: 0,
            budget,
        }
    }

    pub fn get(&self, key: &K) -> Option<CachedObject> {
        self.map.get(key).cloned()
    }

    pub fn put(&mut self, key: K, ty: ObjType, content: Rc<Vec<u8>>) {
        if self.bytes + content.len() > self.budget {
            self.map.clear();
            self.bytes = 0;
        }
        self.bytes += content.len();
        self.map.insert(key, (ty, content));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn blob(n: usize) -> Rc<Vec<u8>> {
        Rc::new(vec![0u8; n])
    }

    #[test]
    fn caches_within_budget() {
        let mut c = ByteBudgetCache::new(100);
        c.put("a", ObjType::Blob, blob(40));
        c.put("b", ObjType::Tree, blob(40));
        assert!(c.get(&"a").is_some());
        assert_eq!(c.get(&"b").unwrap().0, ObjType::Tree);
        assert!(c.get(&"c").is_none());
    }

    #[test]
    fn over_budget_insert_flushes_everything() {
        let mut c = ByteBudgetCache::new(100);
        c.put("a", ObjType::Blob, blob(60));
        c.put("b", ObjType::Blob, blob(60)); // 120 > 100: flush, then insert
        assert!(c.get(&"a").is_none(), "prior entries dropped");
        assert!(c.get(&"b").is_some(), "new entry cached after flush");
        // The flush also reset the byte count: another small insert fits.
        c.put("c", ObjType::Blob, blob(30));
        assert!(c.get(&"b").is_some());
        assert!(c.get(&"c").is_some());
    }

    #[test]
    fn oversized_single_object_still_cached_once() {
        // An object bigger than the whole budget flushes and then occupies
        // the cache alone (it was just materialized; keeping it costs no
        // extra copy since content is shared via Rc).
        let mut c = ByteBudgetCache::new(100);
        c.put("big", ObjType::Blob, blob(500));
        assert!(c.get(&"big").is_some());
    }
}
