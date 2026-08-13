ALTER TABLE posts ADD COLUMN parent_id INTEGER REFERENCES posts(id) ON DELETE SET NULL;
CREATE INDEX posts_parent_id ON posts (parent_id);
