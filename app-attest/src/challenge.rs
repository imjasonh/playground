//! One-time server challenges (replay protection).

use rand_core::{OsRng, RngCore};

use crate::b64;
use crate::error::Error;
use crate::store::{ChallengeRecord, ChallengeStore};

/// Challenge lifetime, in seconds.
pub const CHALLENGE_TTL_SECONDS: u64 = 5 * 60;

/// Fresh random challenge (32 bytes, unpadded base64url).
pub fn generate() -> String {
    let mut bytes = [0u8; 32];
    OsRng.fill_bytes(&mut bytes);
    b64::encode_url(bytes)
}

/// Persist a newly issued challenge.
pub async fn issue(store: &dyn ChallengeStore, now_unix: u64) -> Result<(String, u64), Error> {
    let challenge = generate();
    let expires_at = now_unix.saturating_add(CHALLENGE_TTL_SECONDS);
    store
        .put_challenge(
            &challenge,
            &ChallengeRecord {
                challenge: challenge.clone(),
                expires_at,
            },
        )
        .await
        .map_err(|e| Error::Store(e.0))?;
    Ok((challenge, expires_at))
}

/// Consume `challenge` if it is stored and not expired.
pub async fn consume(
    store: &dyn ChallengeStore,
    challenge: &str,
    now_unix: u64,
) -> Result<(), Error> {
    let record = store
        .take_challenge(challenge)
        .await
        .map_err(|e| Error::Store(e.0))?
        .ok_or(Error::Challenge)?;
    if record.expires_at <= now_unix || record.challenge != challenge {
        return Err(Error::Challenge);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::InMemoryStore;

    #[test]
    fn generate_is_url_safe() {
        let c = generate();
        assert!(!c.contains('+') && !c.contains('/') && !c.contains('='));
        assert_eq!(b64::decode(&c).unwrap().len(), 32);
    }

    #[test]
    fn consume_is_one_shot() {
        let store = InMemoryStore::new();
        futures::executor::block_on(async {
            let (challenge, _) = issue(&store, 1_000).await.unwrap();
            consume(&store, &challenge, 1_001).await.unwrap();
            assert!(consume(&store, &challenge, 1_002).await.is_err());
        });
    }

    #[test]
    fn expired_challenge_fails() {
        let store = InMemoryStore::new();
        futures::executor::block_on(async {
            let (challenge, _) = issue(&store, 1_000).await.unwrap();
            assert!(
                consume(&store, &challenge, 1_000 + CHALLENGE_TTL_SECONDS + 1)
                    .await
                    .is_err()
            );
        });
    }
}
