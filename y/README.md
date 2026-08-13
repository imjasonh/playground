# y

A one-user microblog. 260-char posts, optional images, RSS, email. No JS on the
public site, no tracking.

Built on Cloudflare Workers in **Rust**. D1 for posts/subscribers/passkeys, R2
for images.

Source idea: <https://github.com/imjasonh/ideas/issues/139>

Moved into this playground from [`imjasonh/y`](https://github.com/imjasonh/y)
and rewritten in Rust to match the other Worker apps. It is **not** a GitHub
Pages app (no `index.html`). `deploy-workers.yml` deploys it on pushes to
`main` as Worker `y` on the same Cloudflare account it already runs on
(`https://y.imjasonh.workers.dev`).

Existing D1/R2 bindings and secrets (`ADMIN_PASSWORD_HASH`, `SESSION_SECRET`)
are reused. Password hashes stay `pbkdf2$iters$saltHex$hashHex`. Passkeys are
ES256 with user verification required; stored COSE keys in D1 are unchanged.
WebAuthn challenges travel in a signed cookie and are claimed once at verify
(`webauthn_used_challenges`); options does not need a prior D1 write to be
visible. Missing or empty secrets fail closed (the Worker returns 500) rather
than signing sessions with an empty HMAC key.

## One-time setup

```sh
# 1. D1
wrangler d1 create y
# → copy database_id into wrangler.toml

# 2. R2
wrangler r2 bucket create y-images

# 3. Migrations
wrangler d1 migrations apply y --local     # for `wrangler dev`
wrangler d1 migrations apply y --remote    # for production (also run by deploy)

# 4. Secrets
cargo run --example hash-password -- 'your-admin-password' | \
  wrangler secret put ADMIN_PASSWORD_HASH

openssl rand -hex 32 | wrangler secret put SESSION_SECRET
```

For `wrangler dev`, copy `.dev.vars.example` to `.dev.vars` and fill in.

## Vars

Edit `wrangler.toml` `[vars]`:

- `SITE_TITLE` — header text
- `SITE_URL`   — absolute base URL (used in OG tags, RSS, WebAuthn origin)
- `MAIL_FROM`  — From address for post emails. Empty disables sending.
  Must be a domain verified for [Cloudflare Email Sending](https://developers.cloudflare.com/email-service/)
  (you cannot send from `*.workers.dev`). Set SPF/DKIM on that domain, then
  put the address here (e.g. `posts@example.com`).

## Develop

```sh
cd y
cargo test
cargo fmt --check
cargo clippy --all-targets
npx wrangler dev   # or: wrangler dev
# open http://localhost:8787
# /admin/login with the password whose hash you set in .dev.vars
# Set SITE_URL in wrangler.toml to the origin you browse (localhost when using wrangler dev).

# Optional: workerd/miniflare HTTP smoke (builds wasm, applies local D1 migrations)
./scripts/e2e.sh
```

## Deploy

Pushes to `main` that touch `y/` are deployed by `deploy-workers.yml`. Locally:

```sh
npx wrangler deploy
```

## Routes

Public:
- `/`                          timeline
- `/post/:id`                  permalink with OpenGraph meta
- `/feed.xml`                  RSS 2.0
- `/img/:key+`                 R2-backed image
- `/subscribe`                 email signup
- `/unsubscribe?token=…`       confirm + one-click unsubscribe

Admin (cookie-gated):
- `/admin/login`, `/admin/logout`
- `/admin`                     compose
- `POST /admin/posts`          multipart: `body` + zero-or-more `image`
- `POST /admin/posts/:id/delete`
- `/admin/passkeys`            WebAuthn registration

About a minute after each publish, a cron emails everyone who is not
unsubscribed, unless the post was deleted in that window. Each message
includes a per-subscriber unsubscribe link. Set `MAIL_FROM` to actually
send; until then the cron no-ops (queued posts send once it is set).

## Out of scope

Videos, likes, multi-user, search, drafts. Replies (threads) are supported.
