//! Coordination primitives shared by OTA and optional observability senders.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

static OTA_DOWNLOAD_IN_PROGRESS: AtomicBool = AtomicBool::new(false);

pub struct OtaDownloadGuard;

impl OtaDownloadGuard {
    pub fn enter() -> Self {
        OTA_DOWNLOAD_IN_PROGRESS.store(true, Ordering::Release);
        Self
    }
}

impl Drop for OtaDownloadGuard {
    fn drop(&mut self) {
        OTA_DOWNLOAD_IN_PROGRESS.store(false, Ordering::Release);
    }
}

pub fn ota_download_in_progress() -> bool {
    OTA_DOWNLOAD_IN_PROGRESS.load(Ordering::Acquire)
}

pub type ShortHttpsLock = Arc<Mutex<()>>;

pub fn new_short_https_lock() -> ShortHttpsLock {
    Arc::new(Mutex::new(()))
}
