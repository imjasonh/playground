# playground

A personal playground monorepo for small, self-contained side projects — browser
toys, command-line tools, and the occasional backend service — collected in one
place for fun and learning. There's no grand plan and no shared build at the
root: each experiment is its own top-level directory that builds, tests, and
ships entirely on its own, whether it's a static browser app deployed to GitHub
Pages, a standalone Go command-line tool, or a Rust crate such as a Cloudflare
Worker.

The point is to keep trying things cheap and low-ceremony. Drop in a new
directory, follow a couple of conventions, and open a PR: CI tests whatever
changed, browser apps get a live preview link, and once merged they deploy
themselves to GitHub Pages. A daily job keeps each project's dependencies current
too, landing an upgrade only when it still builds and passes tests — so older
experiments don't bit-rot.

## Apps

- **[`artillery/`](artillery/)** — a touch-first, turn-based artillery duel with
  shifting wind, destructible terrain, local multiplayer, and an imperfect AI.
- **[`git/`](git/)** — an in-browser, read-only git client: clone a repository
  into local storage and browse its files, branches, and commit history.
- **[`cold-climb/`](cold-climb/)** — a touch-first, two-handle arcade game:
  balance a ball up the wall while avoiding unlit pockets.
- **[`hello/`](hello/)** — a minimal static demo.
- **[`kanoodle/`](kanoodle/)** — the Kanoodle puzzle game (5×11 board, 12 pieces).
- **[`nypd-choppers/`](nypd-choppers/)** — daily flight paths, airborne hours,
  and estimated fuel cost for NYPD Aviation Unit helicopters, from public ADS-B
  data collected by an hourly scrape workflow.
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
