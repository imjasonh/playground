# y — one-user microblog

A single-author microblog on Cloudflare Workers. RSS + email subscribers,
260-char posts, images, OG previews, no JS, no tracking.

Source: https://github.com/imjasonh/ideas/issues/139

## Decisions

- **Runtime:** Cloudflare Workers (paid). Rust (`worker` 0.8).
- **Storage:** D1 for posts, image metadata, subscribers. R2 for image bytes.
- **Email:** Cloudflare Email Sending — `env.EMAIL.send({...})` via the
  `[[send_email]]` binding. **Caveat:** requires a domain on Cloudflare DNS
  with MX/SPF/DKIM/DMARC records (cannot send from `*.workers.dev`).
  Phase 1 ships without working email; Phase 2 attaches a custom domain.
- **Auth:** Password-protected `/admin` with a signed cookie session. Single
  user; password held as a Wrangler secret (PBKDF2-HMAC-SHA256). After the
  first passkey is registered, login is WebAuthn-only.
- **Image upload:** `multipart/form-data` to `POST /admin/posts` — Worker
  writes bytes to R2 and rows to D1 in one request.
- **Domain:** `*.workers.dev` for development; custom Cloudflare-managed
  domain required to ship email.

## Schema (D1)

```sql
CREATE TABLE posts (
  id          INTEGER PRIMARY KEY AUTOINCREMENT,
  body        TEXT NOT NULL,            -- <= 260 chars, validated
  created_at  INTEGER NOT NULL          -- unix seconds
);
CREATE INDEX posts_created_at ON posts (created_at DESC);

CREATE TABLE post_images (
  id           INTEGER PRIMARY KEY AUTOINCREMENT,
  post_id      INTEGER NOT NULL REFERENCES posts(id) ON DELETE CASCADE,
  r2_key       TEXT NOT NULL,           -- e.g. "img/<post>/<n>.<ext>"
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
  status       TEXT NOT NULL,            -- 'pending' | 'confirmed' | 'unsubscribed'
  token        TEXT NOT NULL,            -- random; confirm + unsubscribe links
  created_at   INTEGER NOT NULL,
  confirmed_at INTEGER
);
```

## Routes

Public:
- `GET  /`                       — timeline (latest N, paginated)
- `GET  /post/:id`               — single post w/ OpenGraph meta
- `GET  /img/:key+`              — serve R2 object
- `GET  /feed.xml`               — RSS 2.0
- `GET  /subscribe`              — form
- `POST /subscribe`              — creates pending subscriber, sends confirm email
- `GET  /confirm?token=…`        — flips to confirmed
- `GET  /unsubscribe?token=…`    — flips to unsubscribed

Admin (password-gated, cookie):
- `GET  /admin/login`            — password form
- `POST /admin/login`            — sets session cookie
- `POST /admin/logout`
- `GET  /admin`                  — compose + recent posts
- `POST /admin/posts`            — multipart: `body` + zero-or-more `image` files;
                                   writes R2, inserts D1, fans out emails (waitUntil)
- `POST /admin/posts/:id/delete` — hard delete (also drops R2 objects)

## Email sending (Cloudflare)

`wrangler.toml`:
```toml
[[send_email]]
name = "EMAIL"
```

On new post, query confirmed subscribers and call `env.EMAIL.send` per
recipient inside `ctx.waitUntil`. Each message includes a per-subscriber
`/unsubscribe?token=…` link. From address: `posts@<your-domain>`.

On `POST /subscribe`, insert pending row + token, send confirm email with a
`/confirm?token=…` link.

## Templates / styling

- Server-rendered HTML via Hono's `html` tagged template.
- One `<style>` block embedded in the layout — no external CSS, no JS.
- OG tags on `/post/:id`: `og:title` (truncated body), `og:description`,
  `og:image` (first image, absolute URL), `og:type=article`, `twitter:card`.

## Out of scope (issue says "meh")

- Video uploads
- Likes / replies / RTs
- Multi-user
- Search, drafts, scheduling

## Work order

1. Scaffold Wrangler + `package.json` + TS config + Hono.
2. `wrangler.toml`: D1, R2, EMAIL bindings; secrets list.
3. Initial migration SQL + `migrations/0001_init.sql`.
4. Layout, index, single-post views with OG.
5. Image serving route.
6. RSS feed.
7. Admin: session helpers, login, compose, create-post (R2 upload),
   delete-post.
8. Subscribe / confirm / unsubscribe routes (no email yet).
9. Wire `env.EMAIL.send` for confirm + new-post fan-out.
10. README with deploy steps + email DNS setup.
