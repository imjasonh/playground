-- One-time WebAuthn use-marks, claimed on verify.
--
-- The signed y_challenge cookie is the challenge transport. Verify INSERTs
-- here (ON CONFLICT DO NOTHING RETURNING) so the first login does not depend
-- on the options request's D1 write being visible on a replica, and does not
-- depend on D1ResultMeta.changes (which the Worker binding may omit).
-- webauthn_challenges (0004) is no longer written.
CREATE TABLE webauthn_used_challenges (
  challenge TEXT PRIMARY KEY,
  used_at   INTEGER NOT NULL
);
