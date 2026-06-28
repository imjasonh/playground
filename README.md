# playground

A multi-app playground: each top-level directory is a self-contained,
client-side browser app deployed to GitHub Pages. Apps are independent — there
is no shared build step at the repo root.

## Apps

- **[`git/`](git/)** — an in-browser, read-only git client: clone a repository
  into local storage and browse its files, branches, and commit history.
- **[`hello/`](hello/)** — a minimal static demo.
- **[`kanoodle/`](kanoodle/)** — the Kanoodle puzzle game (5×11 board, 12 pieces).

See [`AGENTS.md`](AGENTS.md) for repository conventions, CI, and how to add a new app.
