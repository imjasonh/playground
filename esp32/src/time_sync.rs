//! Wall-clock synchronization for services such as GCP JWT authentication.

use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use esp_idf_svc::sntp::{EspSntp, SyncStatus};

/// Start SNTP, wait up to `timeout` for the first synchronization, and return
/// the live handle.
///
/// Signed OTA uses Rekor's offline-authenticated integrated time and does not
/// depend on this clock. Callers must retain the returned handle for the
/// process lifetime so periodic synchronization stays active.
pub fn start_and_wait(timeout: Duration) -> Result<EspSntp<'static>> {
    let sntp = EspSntp::new_default().context("start SNTP")?;
    let started = Instant::now();
    loop {
        if sntp.get_sync_status() == SyncStatus::Completed {
            tracing::info!(
                elapsed_ms = started.elapsed().as_millis() as u64,
                "ntp: synced",
            );
            break;
        }
        if started.elapsed() > timeout {
            tracing::warn!(
                timeout_secs = timeout.as_secs(),
                "ntp: not synced; wall-clock-dependent services remain unavailable",
            );
            break;
        }
        std::thread::sleep(Duration::from_millis(200));
    }
    Ok(sntp)
}
