# playground

A multi-app playground: each top-level directory is either a self-contained
browser app deployed to GitHub Pages or an independent Go command-line app.
There is no shared build step at the repo root.

## Apps

- **[`git/`](git/)** — an in-browser, read-only git client: clone a repository
  into local storage and browse its files, branches, and commit history.
- **[`hello/`](hello/)** — a minimal static demo.
- **[`kanoodle/`](kanoodle/)** — the Kanoodle puzzle game (5×11 board, 12 pieces).

## Tools

Not every top-level directory is a browser app. Go command-line tools live here
too. CI builds and tests each changed Go module; because these tools have no
`index.html`, GitHub Pages deploy and preview workflows skip them:

- **[`ocidb/`](ocidb/)** — explore OCI container images on Docker Hub with SQL,
  via SQLite virtual tables over go-containerregistry (Go CLI).

See [`AGENTS.md`](AGENTS.md) for repository conventions, CI, and how to add a new app.
