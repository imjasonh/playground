//! OTA slot state: pending-verify, digest cache, rollback.
//!
//! Shared by the inkbot poller (Worker fetch is the health check) and
//! the maze firmware (first successful panel paint is the health check).

use anyhow::{bail, Context, Result};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs, NvsDefault};

use crate::nvs_util::read_str;

pub(crate) const NVS_NAMESPACE: &str = "ota";
const NVS_LAST_DIGEST: &str = "last_digest";
const NVS_PENDING_DIGEST: &str = "pending_digest";
const NVS_DIGEST_BUF: usize = 96;

pub fn is_pending_verify() -> bool {
    use esp_idf_svc::sys::*;
    unsafe {
        let part = esp_ota_get_running_partition();
        if part.is_null() {
            return false;
        }
        let mut state: esp_ota_img_states_t = 0;
        let err = esp_ota_get_state_partition(part, &mut state);
        if err != ESP_OK {
            log::warn!("ota: esp_ota_get_state_partition failed {err}");
            return false;
        }
        state == esp_ota_img_states_t_ESP_OTA_IMG_PENDING_VERIFY
    }
}

/// If this boot is not `PENDING_VERIFY` but `pending_digest` is still set,
/// the previous image rolled back. Record that digest as `last_digest` so
/// the next poll does not re-flash the same binary.
pub fn remember_rolled_back_digest(nvs_partition: EspDefaultNvsPartition) -> Result<()> {
    if is_pending_verify() {
        return Ok(());
    }
    persist_pending_as_last(nvs_partition)
}

fn persist_pending_as_last(nvs_partition: EspDefaultNvsPartition) -> Result<()> {
    let mut nvs =
        EspNvs::new(nvs_partition, NVS_NAMESPACE, true).context("open ota NVS namespace")?;
    if let Some(pending) = read_digest_pending(&nvs) {
        write_string(&mut nvs, NVS_LAST_DIGEST, &pending)?;
        let _ = nvs.remove(NVS_PENDING_DIGEST);
        log::info!("ota: recorded rejected digest {pending} (skip until GHCR changes)");
    }
    Ok(())
}

pub fn mark_valid_after_pending_verify_passed(nvs_partition: EspDefaultNvsPartition) -> Result<()> {
    use esp_idf_svc::sys::*;
    let err = unsafe { esp_ota_mark_app_valid_cancel_rollback() };
    if err != ESP_OK {
        bail!("esp_ota_mark_app_valid_cancel_rollback err={err}");
    }
    log::info!("ota: marked app valid, rollback cancelled");

    let mut nvs =
        EspNvs::new(nvs_partition, NVS_NAMESPACE, true).context("open ota NVS namespace")?;
    if let Some(pending) = read_digest_pending(&nvs) {
        write_string(&mut nvs, NVS_LAST_DIGEST, &pending)?;
        let _ = nvs.remove(NVS_PENDING_DIGEST);
        log::info!("ota: promoted pending -> last_digest {pending}");
    }
    Ok(())
}

/// Persist the pending digest as rejected, then ask the bootloader to
/// roll back. Does not return on success.
pub fn reject_pending_and_reboot(nvs_partition: EspDefaultNvsPartition) -> ! {
    if let Err(e) = persist_pending_as_last(nvs_partition) {
        log::error!("ota: persist rejected digest failed: {e:#}");
    }
    let err = unsafe { esp_idf_svc::sys::esp_ota_mark_app_invalid_rollback_and_reboot() };
    log::error!("ota: mark_invalid returned {err}; restarting");
    unsafe { esp_idf_svc::sys::esp_restart() }
}

#[cfg(feature = "ota-pull")]
pub(crate) fn read_last_digest(nvs: &EspNvs<NvsDefault>) -> Option<String> {
    read_str(nvs, NVS_NAMESPACE, NVS_LAST_DIGEST, NVS_DIGEST_BUF)
        .ok()
        .flatten()
}

#[cfg(feature = "ota-pull")]
pub(crate) fn write_pending_digest(nvs: &mut EspNvs<NvsDefault>, digest: &str) -> Result<()> {
    write_string(nvs, NVS_PENDING_DIGEST, digest)
}

#[cfg(feature = "ota-pull")]
pub(crate) fn write_last_digest(nvs: &mut EspNvs<NvsDefault>, digest: &str) -> Result<()> {
    write_string(nvs, NVS_LAST_DIGEST, digest)
}

fn write_string(nvs: &mut EspNvs<NvsDefault>, key: &str, value: &str) -> Result<()> {
    nvs.set_str(key, value)
        .with_context(|| format!("write NVS key {key}"))
}

fn read_digest_pending(nvs: &EspNvs<NvsDefault>) -> Option<String> {
    read_str(nvs, NVS_NAMESPACE, NVS_PENDING_DIGEST, NVS_DIGEST_BUF)
        .ok()
        .flatten()
}
