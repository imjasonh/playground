//! Transient STL blob storage.
//!
//! Production backs this with R2; tests use [`InMemoryStore`]. Blobs are keyed
//! by a random hex id and served at `/files/{id}` so Slant can fetch them
//! during a slice request.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use async_trait::async_trait;

/// Storage failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoreError(pub String);

impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for StoreError {}

/// Put / get / delete binary STL blobs by id.
///
/// Futures are `?Send` because the Workers runtime is single-threaded and its
/// types are not `Send` (same pattern as `web-push`).
#[async_trait(?Send)]
pub trait StlStore {
    async fn put(&self, id: &str, bytes: Vec<u8>) -> Result<(), StoreError>;
    async fn get(&self, id: &str) -> Result<Option<Vec<u8>>, StoreError>;
    async fn delete(&self, id: &str) -> Result<(), StoreError>;
}

/// Process-local store for tests.
#[derive(Clone, Default)]
pub struct InMemoryStore {
    inner: Arc<Mutex<HashMap<String, Vec<u8>>>>,
}

impl InMemoryStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.inner.lock().map(|g| g.len()).unwrap_or(0)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[async_trait(?Send)]
impl StlStore for InMemoryStore {
    async fn put(&self, id: &str, bytes: Vec<u8>) -> Result<(), StoreError> {
        self.inner
            .lock()
            .map_err(|e| StoreError(e.to_string()))?
            .insert(id.to_string(), bytes);
        Ok(())
    }

    async fn get(&self, id: &str) -> Result<Option<Vec<u8>>, StoreError> {
        Ok(self
            .inner
            .lock()
            .map_err(|e| StoreError(e.to_string()))?
            .get(id)
            .cloned())
    }

    async fn delete(&self, id: &str) -> Result<(), StoreError> {
        self.inner
            .lock()
            .map_err(|e| StoreError(e.to_string()))?
            .remove(id);
        Ok(())
    }
}

/// Generate a 128-bit random hex id (32 lowercase hex chars).
pub fn new_file_id() -> Result<String, StoreError> {
    let mut bytes = [0u8; 16];
    getrandom::getrandom(&mut bytes).map_err(|e| StoreError(e.to_string()))?;
    Ok(bytes.iter().map(|b| format!("{b:02x}")).collect())
}
