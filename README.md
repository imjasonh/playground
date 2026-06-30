# playground

A multi-app playground: each top-level directory is a self-contained browser app
deployed to GitHub Pages, an independent Go command-line app, or a Rust app (such
as a Cloudflare Worker). There is no shared build step at the repo root.

## Apps

- **[`git/`](git/)** — an in-browser, read-only git client: clone a repository
  into local storage and browse its files, branches, and commit history.
- **[`hello/`](hello/)** — a minimal static demo.
- **[`kanoodle/`](kanoodle/)** — the Kanoodle puzzle game (5×11 board, 12 pieces).
- **[`web-push-demo/`](web-push-demo/)** — a browser front-end for the
  `web-push` Worker: subscribe/unsubscribe and send notifications end to end.

## Tools

Not every top-level directory is a browser app. Go command-line tools and Rust
apps live here too. CI builds and tests each changed Go module and Rust crate;
because these have no `index.html`, GitHub Pages deploy and preview workflows
skip them:

- **[`gitdb/`](gitdb/)** — query a git repo's history, files, blame, and file
  contents with SQL, via SQLite virtual tables over go-git (Go CLI).
- **[`ocidb/`](ocidb/)** — explore OCI container images on Docker Hub with SQL,
  via SQLite virtual tables over go-containerregistry (Go CLI).
- **[`web-push/`](web-push/)** — a Web Push application-server backend
  (RFC 8030/8188/8291/8292) for Cloudflare Workers, in Rust.

See [`AGENTS.md`](AGENTS.md) for repository conventions, CI, and how to add a new app.
