CREATE TABLE posts (
  id          INTEGER PRIMARY KEY AUTOINCREMENT,
  body        TEXT NOT NULL,
  created_at  INTEGER NOT NULL
);

CREATE INDEX posts_created_at ON posts (created_at DESC);

CREATE TABLE post_images (
  id           INTEGER PRIMARY KEY AUTOINCREMENT,
  post_id      INTEGER NOT NULL REFERENCES posts(id) ON DELETE CASCADE,
  r2_key       TEXT NOT NULL,
  content_type TEXT NOT NULL,
  width        INTEGER,
  height       INTEGER,
  alt          TEXT,
  ordinal      INTEGER NOT NULL
);

CREATE INDEX post_images_post_id ON post_images (post_id, ordinal);

CREATE TABLE subscribers (
  id           INTEGER PRIMARY KEY AUTOINCREMENT,
  email        TEXT NOT NULL UNIQUE,
  status       TEXT NOT NULL CHECK (status IN ('pending', 'confirmed', 'unsubscribed')),
  token        TEXT NOT NULL,
  created_at   INTEGER NOT NULL,
  confirmed_at INTEGER
);

CREATE INDEX subscribers_status ON subscribers (status);
CREATE INDEX subscribers_token ON subscribers (token);
