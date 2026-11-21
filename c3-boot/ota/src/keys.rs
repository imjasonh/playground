//! Ed25519 development keys stored as hex seeds.
//!
//! Production trust-root keys live on hardware tokens. Seed files are for
//! tests and development only.

use ed25519_dalek::SigningKey;

/// Parses a 64-character hex seed, ignoring surrounding whitespace.
pub fn signing_key_from_hex(text: &str) -> Result<SigningKey, String> {
    let hex = text.trim();
    if hex.len() != 64 {
        return Err("a seed is 64 hex characters".into());
    }
    let mut seed = [0u8; 32];
    for (i, byte) in seed.iter_mut().enumerate() {
        let pair = hex.get(2 * i..2 * i + 2).ok_or("short seed")?;
        *byte = u8::from_str_radix(pair, 16).map_err(|e| e.to_string())?;
    }
    Ok(SigningKey::from_bytes(&seed))
}

/// Reads a seed file.
pub fn read_signing_key(path: &str) -> Result<SigningKey, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    signing_key_from_hex(&text)
}
