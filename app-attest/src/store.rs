//! Storage traits for challenges and attested devices.
//!
//! The API logic is written against these traits so it can run over Cloudflare
//! Workers KV in production and an in-memory map in tests. Trait methods use
//! `?Send` futures because the Workers runtime is single-threaded.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;

use async_trait::async_trait;
use serde::{Deserialize, Serialize};

/// An opaque storage error.
#[derive(Debug, Clone)]
pub struct StoreError(pub String);

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "store error: {}", self.0)
    }
}

impl std::error::Error for StoreError {}

/// A one-time challenge waiting to be consumed.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChallengeRecord {
    pub challenge: String,
    pub expires_at: u64,
}

/// An attested device row bound to a user.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DeviceRecord {
    pub key_id: String,
    pub user_id: String,
    pub device_id: String,
    /// Uncompressed P-256 public key (SEC1, 65 bytes), standard base64.
    pub public_key: String,
    pub counter: u32,
    pub created_at: u64,
}

/// One-time challenge store. `take` deletes the row so a nonce cannot replay.
#[async_trait(?Send)]
pub trait ChallengeStore {
    async fn put_challenge(&self, id: &str, record: &ChallengeRecord) -> Result<(), StoreError>;
    async fn take_challenge(&self, id: &str) -> Result<Option<ChallengeRecord>, StoreError>;
}

/// Persistent mapping from App Attest `keyId` to a user and device.
#[async_trait(?Send)]
pub trait DeviceStore {
    async fn put_device(&self, record: &DeviceRecord) -> Result<(), StoreError>;
    async fn get_device(&self, key_id: &str) -> Result<Option<DeviceRecord>, StoreError>;
}

/// Combined store used by the HTTP API.
pub trait AttestStore: ChallengeStore + DeviceStore {}

impl<T> AttestStore for T where T: ChallengeStore + DeviceStore {}

/// In-memory store for tests.
#[derive(Default)]
pub struct InMemoryStore {
    challenges: RefCell<HashMap<String, ChallengeRecord>>,
    devices: RefCell<HashMap<String, DeviceRecord>>,
}

impl InMemoryStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn device_count(&self) -> usize {
        self.devices.borrow().len()
    }
}

#[async_trait(?Send)]
impl ChallengeStore for InMemoryStore {
    async fn put_challenge(&self, id: &str, record: &ChallengeRecord) -> Result<(), StoreError> {
        self.challenges
            .borrow_mut()
            .insert(id.to_string(), record.clone());
        Ok(())
    }

    async fn take_challenge(&self, id: &str) -> Result<Option<ChallengeRecord>, StoreError> {
        Ok(self.challenges.borrow_mut().remove(id))
    }
}

#[async_trait(?Send)]
impl DeviceStore for InMemoryStore {
    async fn put_device(&self, record: &DeviceRecord) -> Result<(), StoreError> {
        self.devices
            .borrow_mut()
            .insert(record.key_id.clone(), record.clone());
        Ok(())
    }

    async fn get_device(&self, key_id: &str) -> Result<Option<DeviceRecord>, StoreError> {
        Ok(self.devices.borrow().get(key_id).cloned())
    }
}
