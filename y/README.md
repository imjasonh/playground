# y

A one-user microblog. 260-char posts, optional images, RSS, email
subscribers. No JS on the public site, no tracking.

Built on Cloudflare Workers (Hono). D1 for posts/subscribers, R2 for images,
Cloudflare Email Sending for subscriber confirmations + new-post fan-out.

Source idea: <https://github.com/imjasonh/ideas/issues/139>

Moved into this playground from [`imjasonh/y`](https://github.com/imjasonh/y).
It is **not** a GitHub Pages app (no `index.html`). `deploy-workers.yml`
deploys it on pushes to `main` as Worker `y` on the same Cloudflare account
it already runs on (`https://y.imjasonh.workers.dev`).

## One-time setup

```sh
npm install

# 1. D1
wrangler d1 create y
# → copy database_id into wrangler.toml

# 2. R2
wrangler r2 bucket create y-images

# 3. Migrations
npm run migrate:local        # for `wrangler dev`
npm run migrate:remote       # for production

# 4. Secrets
node scripts/hash-password.mjs 'your-admin-password' | \
  wrangler secret put ADMIN_PASSWORD_HASH

openssl rand -hex 32 | wrangler secret put SESSION_SECRET
```

For `wrangler dev`, copy `.dev.vars.example` to `.dev.vars` and fill in.

## Vars

Edit `wrangler.toml` `[vars]`:

- `SITE_TITLE` — header text and email subject prefix
- `SITE_URL`   — absolute base URL (used in OG tags, RSS, email links)
- `FROM_EMAIL` — sender for confirmation + notification emails
- `FROM_NAME`  — display name for the sender (optional)

## Email setup (required for subscriber emails)

Cloudflare Email Sending requires a domain on Cloudflare DNS with the right
records. Without this, posts still work, but confirmation and notification
emails will fail (silently logged via `wrangler tail`).

1. Add your domain to Cloudflare DNS.
2. Dashboard → **Email** → **Email Sending** → add the MX/SPF/DKIM/DMARC
   records on `cf-bounce.<your-domain>`.
3. Wait for propagation (5–15 min typical).
4. Set `FROM_EMAIL` to an address on your domain, e.g. `posts@your-domain`.
5. Add a custom route to your Worker so `SITE_URL` matches the deployed
   domain. Confirmation links must be HTTPS on a real domain — `*.workers.dev`
   is fine for the site itself, but the `From:` address has to live on a
   verified domain.

Reference: <https://developers.cloudflare.com/email-service/get-started/send-emails/>

## Develop

```sh
npm run dev
# open http://localhost:8787
# /admin/login with the password whose hash you set in .dev.vars
```

## Deploy

```sh
npm run deploy
```

## Routes

Public:
- `/`                          timeline
- `/post/:id`                  permalink with OpenGraph meta
- `/feed.xml`                  RSS 2.0
- `/img/:key+`                 R2-backed image
- `/subscribe`, `/confirm?token=…`, `/unsubscribe?token=…`

Admin (cookie-gated):
- `/admin/login`, `/admin/logout`
- `/admin`                     compose + recent posts
- `POST /admin/posts`          multipart: `body` + zero-or-more `image`
- `POST /admin/posts/:id/delete`

## Out of scope

Videos, likes, replies, multi-user, search, drafts. By design.
