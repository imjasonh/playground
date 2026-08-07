use anyhow::{Context, Result, anyhow};
use base64::{Engine as _, engine::general_purpose};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs};
use sha2::{Digest, Sha256};
use sunset::{KeyType, PubKey, SignKey};
use zeroize::Zeroize;

use esp32_blinky::nvs_util::{read_blob, read_str};

const NAMESPACE: &str = "ssh";
const HOST: &str = "host";
const PORT: &str = "port";
const USERNAME: &str = "username";
const HOST_KEY: &str = "host_key";
const COMMAND: &str = "command";
const CLIENT_SEED: &str = "client_seed";

#[derive(Clone, Debug)]
pub struct SshConfig {
    pub host: String,
    pub port: u16,
    pub username: String,
    pub host_key: [u8; 32],
    pub command: String,
}

impl SshConfig {
    pub fn load(partition: EspDefaultNvsPartition) -> Result<Option<Self>> {
        let nvs = match EspNvs::new(partition, NAMESPACE, false) {
            Ok(nvs) => nvs,
            Err(error) if error.code() == esp_idf_svc::sys::ESP_ERR_NVS_NOT_FOUND as i32 => {
                return Ok(None);
            }
            Err(error) => {
                return Err(anyhow!("open NVS namespace {NAMESPACE}: {error:?}"));
            }
        };
        let host = read_str(&nvs, NAMESPACE, HOST, 256)?;
        let username = read_str(&nvs, NAMESPACE, USERNAME, 96)?;
        let command = read_str(&nvs, NAMESPACE, COMMAND, 512)?;
        let host_key = read_blob(&nvs, NAMESPACE, HOST_KEY, 64)?;
        let port = nvs
            .get_u16(PORT)
            .map_err(|e| anyhow!("read NVS {NAMESPACE}/{PORT}: {e:?}"))?;

        let (Some(host), Some(username), Some(command), Some(host_key), Some(port)) =
            (host, username, command, host_key, port)
        else {
            return Ok(None);
        };

        let host_key: [u8; 32] = host_key.try_into().map_err(|value: Vec<u8>| {
            anyhow!(
                "NVS {NAMESPACE}/{HOST_KEY} must contain a 32-byte Ed25519 key, got {} bytes",
                value.len()
            )
        })?;

        Ok(Some(Self {
            host,
            port,
            username,
            host_key,
            command,
        }))
    }
}

/// Load the device's Ed25519 seed, or generate and persist one on first boot.
///
/// Call this only after WiFi has started: ESP-IDF's hardware RNG has its
/// strongest entropy source enabled while WiFi or Bluetooth is active.
pub fn load_or_generate_key(partition: EspDefaultNvsPartition) -> Result<SignKey> {
    let nvs = EspNvs::new(partition, NAMESPACE, true)
        .map_err(|e| anyhow!("open writable NVS namespace {NAMESPACE}: {e:?}"))?;

    if let Some(mut seed) = read_blob(&nvs, NAMESPACE, CLIENT_SEED, 64)? {
        let result = seed
            .as_slice()
            .try_into()
            .map(|seed: &[u8; 32]| {
                SignKey::Ed25519(sunset::ed25519_dalek::SigningKey::from_bytes(seed))
            })
            .map_err(|_| {
                anyhow!(
                    "NVS {NAMESPACE}/{CLIENT_SEED} must be 32 bytes, got {}",
                    seed.len()
                )
            });
        seed.zeroize();
        return result;
    }

    let key = SignKey::generate(KeyType::Ed25519, None).context("generate Ed25519 key")?;
    let mut seed = match &key {
        SignKey::Ed25519(key) => key.to_bytes(),
        _ => return Err(anyhow!("Sunset generated a non-Ed25519 key")),
    };
    nvs.set_blob(CLIENT_SEED, &seed)
        .map_err(|e| anyhow!("write NVS {NAMESPACE}/{CLIENT_SEED}: {e:?}"))?;
    seed.zeroize();
    tracing::info!("ssh: generated and persisted a new Ed25519 client key");
    Ok(key)
}

pub fn authorized_key(key: &SignKey) -> Result<String> {
    let blob = public_key_blob(&key.pubkey())?;
    Ok(format!(
        "ssh-ed25519 {} esp32-eink",
        general_purpose::STANDARD.encode(blob)
    ))
}

pub fn fingerprint(key: &SignKey) -> Result<String> {
    let digest = Sha256::digest(public_key_blob(&key.pubkey())?);
    Ok(format!(
        "SHA256:{}",
        general_purpose::STANDARD_NO_PAD.encode(digest)
    ))
}

pub fn host_key_fingerprint(key: &[u8; 32]) -> String {
    let mut blob = Vec::with_capacity(4 + 11 + 4 + 32);
    blob.extend_from_slice(&11_u32.to_be_bytes());
    blob.extend_from_slice(b"ssh-ed25519");
    blob.extend_from_slice(&32_u32.to_be_bytes());
    blob.extend_from_slice(key);
    let digest = Sha256::digest(blob);
    format!("SHA256:{}", general_purpose::STANDARD_NO_PAD.encode(digest))
}

fn public_key_blob(key: &PubKey<'_>) -> Result<Vec<u8>> {
    let PubKey::Ed25519(key) = key else {
        return Err(anyhow!("only Ed25519 client keys are supported"));
    };

    let algorithm = b"ssh-ed25519";
    let mut blob = Vec::with_capacity(4 + algorithm.len() + 4 + 32);
    blob.extend_from_slice(&(algorithm.len() as u32).to_be_bytes());
    blob.extend_from_slice(algorithm);
    blob.extend_from_slice(&(32_u32).to_be_bytes());
    blob.extend_from_slice(&key.key.0);
    Ok(blob)
}
