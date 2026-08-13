// Generated-style ambient bindings. Keep in sync with wrangler.toml.

interface Env {
  DB: D1Database;
  IMAGES: R2Bucket;

  // vars
  SITE_TITLE: string;
  SITE_URL: string;

  // secrets
  ADMIN_PASSWORD_HASH: string;
  SESSION_SECRET: string;
}
