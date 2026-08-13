-- One-time WebAuthn challenges (cookie is still signed; this row is consumed
-- on verify so a captured cookie cannot be replayed for the TTL).
CREATE TABLE webauthn_challenges (
  challenge  TEXT PRIMARY KEY,
  expires_at INTEGER NOT NULL
);

-- Sliding-window counters for bootstrap login and public subscribe.
CREATE TABLE rate_limits (
  key TEXT NOT NULL,
  ts  INTEGER NOT NULL
);

CREATE INDEX rate_limits_key_ts ON rate_limits (key, ts);
