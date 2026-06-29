//! Subscription storage abstraction.
//!
//! The API logic is written against the [`SubscriptionStore`] trait so it can
//! run over Cloudflare Workers KV in production and an in-memory map in tests.
//! Trait methods use `?Send` futures because the Workers runtime is
//! single-threaded and its types are not `Send`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;

use async_trait::async_trait;
use serde::{Deserialize, Serialize};

use crate::subscription::Subscription;

/// A stored subscription plus bookkeeping metadata.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StoredSubscription {
    /// Stable id (see [`Subscription::id`]).
    pub id: String,
    /// The subscription itself.
    pub subscription: Subscription,
    /// Unix timestamp (seconds) the subscription was stored.
    #[serde(default)]
    pub created_at: u64,
}

impl StoredSubscription {
    /// Wrap a subscription, computing its id.
    pub fn new(subscription: Subscription, created_at: u64) -> Self {
        Self {
            id: subscription.id(),
            subscription,
            created_at,
        }
    }
}

/// An opaque storage error.
#[derive(Debug, Clone)]
pub struct StoreError(pub String);

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "subscription store error: {}", self.0)
    }
}

impl std::error::Error for StoreError {}

/// CRUD over stored subscriptions.
#[async_trait(?Send)]
pub trait SubscriptionStore {
    /// Insert or replace a subscription.
    async fn put(&self, sub: &StoredSubscription) -> Result<(), StoreError>;
    /// Fetch a subscription by id.
    async fn get(&self, id: &str) -> Result<Option<StoredSubscription>, StoreError>;
    /// Remove a subscription by id (no error if absent).
    async fn delete(&self, id: &str) -> Result<(), StoreError>;
    /// List all stored subscriptions.
    async fn list(&self) -> Result<Vec<StoredSubscription>, StoreError>;
}

/// A simple in-memory store for tests and local runs.
#[derive(Default)]
pub struct InMemoryStore {
    inner: RefCell<HashMap<String, StoredSubscription>>,
}

impl InMemoryStore {
    /// Create an empty store.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of stored subscriptions.
    pub fn len(&self) -> usize {
        self.inner.borrow().len()
    }

    /// Whether the store is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.borrow().is_empty()
    }
}

#[async_trait(?Send)]
impl SubscriptionStore for InMemoryStore {
    async fn put(&self, sub: &StoredSubscription) -> Result<(), StoreError> {
        self.inner.borrow_mut().insert(sub.id.clone(), sub.clone());
        Ok(())
    }

    async fn get(&self, id: &str) -> Result<Option<StoredSubscription>, StoreError> {
        Ok(self.inner.borrow().get(id).cloned())
    }

    async fn delete(&self, id: &str) -> Result<(), StoreError> {
        self.inner.borrow_mut().remove(id);
        Ok(())
    }

    async fn list(&self) -> Result<Vec<StoredSubscription>, StoreError> {
        Ok(self.inner.borrow().values().cloned().collect())
    }
}
