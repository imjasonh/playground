-- Schedule outbound post mail `NOTIFY_DELAY_SECS` after publish. NULL
-- notify_at (existing rows) means "never email"; notified_at is set after
-- the cron successfully fans out (or finds nobody to send to).
ALTER TABLE posts ADD COLUMN notify_at INTEGER;
ALTER TABLE posts ADD COLUMN notified_at INTEGER;

CREATE INDEX posts_notify_due ON posts (notify_at)
  WHERE notify_at IS NOT NULL AND notified_at IS NULL;
