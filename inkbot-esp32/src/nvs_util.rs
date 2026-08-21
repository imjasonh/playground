//! Typed NVS reads with consistent error context.

use anyhow::{anyhow, Result};
use esp_idf_svc::nvs::{EspNvs, NvsDefault};
#[cfg(feature = "inkbot-lib")]
use esp_idf_svc::sys::EspError;

/// True when `EspNvs::new` failed because the namespace has never been written.
#[cfg(feature = "inkbot-lib")]
pub fn is_not_found(e: &EspError) -> bool {
    e.code() == esp_idf_svc::sys::ESP_ERR_NVS_NOT_FOUND as i32
}

/// Read a NUL-terminated string from `nvs[key]`. Returns `Ok(None)` if
/// the key is absent. `max_len` is the buffer size.
pub fn read_str(
    nvs: &EspNvs<NvsDefault>,
    namespace: &str,
    key: &str,
    max_len: usize,
) -> Result<Option<String>> {
    let mut buf = vec![0u8; max_len];
    Ok(nvs
        .get_str(key, &mut buf)
        .map_err(|e| anyhow!("read NVS {namespace}/{key}: {e:?}"))?
        .map(|s| s.trim_end_matches('\0').to_string())
        .filter(|s| !s.is_empty()))
}

/// Read a blob from `nvs[key]`. Returns `Ok(None)` if the key is absent.
#[cfg(feature = "inkbot-lib")]
pub fn read_blob(
    nvs: &EspNvs<NvsDefault>,
    namespace: &str,
    key: &str,
    max_len: usize,
) -> Result<Option<Vec<u8>>> {
    let mut buf = vec![0u8; max_len];
    Ok(nvs
        .get_blob(key, &mut buf)
        .map_err(|e| anyhow!("read NVS {namespace}/{key}: {e:?}"))?
        .map(|b| b.to_vec()))
}
