CREATE TABLE credentials (
  id            INTEGER PRIMARY KEY AUTOINCREMENT,
  credential_id TEXT NOT NULL UNIQUE,
  public_key    BLOB NOT NULL,
  counter       INTEGER NOT NULL,
  transports    TEXT,
  label         TEXT NOT NULL,
  created_at    INTEGER NOT NULL
);

CREATE INDEX credentials_credential_id ON credentials (credential_id);
