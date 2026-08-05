//! Small helpers for reading typed values out of an NVS namespace.
//!
//! Each module had near-identical `read_str` / `read_blob` wrappers
//! with subtly different error contexts; consolidating them here keeps
//! the error format consistent and lets us tweak buffer sizing in one
//! place.

use anyhow::{anyhow, Result};
use esp_idf_svc::nvs::{EspNvs, NvsDefault};

/// Read a NUL-terminated string from `nvs[key]`. Returns `Ok(None)` if
/// the key is absent. `max_len` is the buffer size; callers should pick
/// it generously (NVS strings up to ~4 KB are cheap).
pub fn read_str(
    nvs: &EspNvs<NvsDefault>,
    namespace: &str,
    key: &str,
    max_len: usize,
) -> Result<Option<String>> {
    let mut buf = vec![0u8; max_len];
    Ok(nvs
        .get_str(key, &mut buf)
        .map_err(|e| anyhow!("read NVS {}/{}: {:?}", namespace, key, e))?
        .map(|s| s.to_string()))
}

/// Read a blob from `nvs[key]`. Returns `Ok(None)` if the key is absent.
pub fn read_blob(
    nvs: &EspNvs<NvsDefault>,
    namespace: &str,
    key: &str,
    max_len: usize,
) -> Result<Option<Vec<u8>>> {
    let mut buf = vec![0u8; max_len];
    Ok(nvs
        .get_blob(key, &mut buf)
        .map_err(|e| anyhow!("read NVS {}/{}: {:?}", namespace, key, e))?
        .map(|b| b.to_vec()))
}
