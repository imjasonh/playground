# Agent guide: playground

This repository is a **multi-app playground**. Each top-level directory can be a
self-contained browser app deployed to GitHub Pages, an independent Go
command-line app, or a Rust app (e.g. a Cloudflare Worker). There is no shared
build step at the repo root.

## Repository layout

```
playground/
├── AGENTS.md              ← you are here
├── README.md
├── .github/
│   ├── pages/             # shared HTML template for app index pages
│   ├── scripts/           # CI helpers: app discovery + index-page rendering
│   └── workflows/         # deploy, preview, test, cleanup, dependency updates
├── artillery/             # touch-first turn-based artillery duel (JS + Node tests)
├── cold-climb/            # touch-first two-handle arcade game (JS + Node tests)
├── cors-proxy/            # Rust Cloudflare Worker: SSRF-hardened CORS proxy (not a Pages app)
├── cors-proxy-demo/       # static browser front-end for the cors-proxy Worker
├── git/                   # in-browser read-only git client (JS + Jest + Playwright)
├── gitdb/                 # Go CLI (Go module + Go tests)
├── hello/                 # example static app (HTML only)
├── kanoodle/              # example app with tests (JS + Jest + Playwright)
├── ocidb/                 # Go CLI (Go module + Go tests)
├── web-push/              # Rust Cloudflare Worker (Cargo + tests; not a Pages app)
└── web-push-demo/         # static browser front-end for the web-push Worker
```

### Browser apps

A top-level directory is a **browser app** when it contains **`index.html`** at
its root. This is the same rule used by deploy and preview workflows.

| Path | Browser app? | Notes |
|------|--------------|-------|
| `artillery/` | yes | Turn-based artillery duel; JS modules, npm scripts, tests |
| `cold-climb/` | yes | Touch-first arcade game; JS modules, npm scripts, tests |
| `cors-proxy-demo/` | yes | Static front-end for `cors-proxy`; HTML/JS, no build or tests |
| `git/` | yes | In-browser read-only git client; JS modules, npm scripts, tests |
| `hello/` | yes | Static HTML; no build or tests |
| `kanoodle/` | yes | Client-side JS modules, npm scripts, tests |
| `web-push-demo/` | yes | Static front-end for `web-push`; HTML/JS, no build or tests |
| `gitdb/` | no | Go CLI; no `index.html` |
| `ocidb/` | no | Go CLI; no `index.html` |
| `web-push/` | no | Rust Cloudflare Worker; no `index.html` |
| `cors-proxy/` | no | Rust Cloudflare Worker; no `index.html` |
| `.github/` | no | Infrastructure only |
| `README.md` | no | Not a directory |

### Go apps

A top-level directory is a **Go app** when it contains **`go.mod`** at its root.
Go apps are command-line tools, not browser apps: do not add `index.html` to a
Go app. They are built and tested by CI but are not copied to GitHub Pages and
do not receive PR preview deployments.

Each Go app is an isolated module. Keep its Go sources, tests, `go.mod`, and
`go.sum` inside its own top-level directory; do not add a repo-root Go module or
`go.work` file.

### Rust apps

A top-level directory is a **Rust app** when it contains **`Cargo.toml`** at its
root. Rust apps (e.g. `web-push`, a Cloudflare Worker) are built, linted, and
tested by CI but are not copied to GitHub Pages and do not receive PR preview
deployments. A Cloudflare Worker app (a Rust app with a `wrangler.toml`) is
instead deployed by `deploy-workers.yml` on pushes to `main` with `wrangler`,
using the repo secrets `CLOUDFLARE_API_TOKEN` and `CLOUDFLARE_ACCOUNT_ID`. A
Rust app may also have a companion browser app that *is* served from Pages —
`web-push` pairs with `web-push-demo`.

Each Rust app is an isolated crate. Keep its sources, tests, `Cargo.toml`, and
`Cargo.lock` inside its own top-level directory; do not add a repo-root crate or
Cargo workspace. Pin the toolchain with a `rust-toolchain.toml` (channel,
components, and any extra targets such as `wasm32-unknown-unknown`) so local
builds and CI agree.

Hidden top-level directories (names starting with `.`) are ignored by all app
discovery scripts.

## GitHub Actions

| Workflow | Trigger | Purpose |
|----------|---------|---------|
| `deploy.yml` | push to `main` | Publishes all browser apps to GitHub Pages production |
| `deploy-workers.yml` | push to `main`, manual | Deploys changed Cloudflare Worker apps (those with `wrangler.toml`) with `wrangler`, using the `CLOUDFLARE_API_TOKEN` and `CLOUDFLARE_ACCOUNT_ID` repo secrets; a manual *Run workflow* (`workflow_dispatch`) redeploys all of them. Before deploy it create-or-gets each Worker's KV namespaces and substitutes the placeholder ids in `wrangler.toml`; after deploy it get-or-generates a `VAPID_PRIVATE_KEY` secret for any Worker shipping an `examples/genvapid.rs` |
| `preview.yml` | pull request opened/sync | Deploys browser apps under `/preview/pr-<N>/` and comments the URL |
| `cleanup.yml` | pull request closed | Removes that PR's preview directory from `gh-pages` and refreshes the root index |
| `test.yml` | push to `main`, pull requests | Tests changed browser, Go, and Rust apps in one job |
| `deps.yaml` | daily at 00:00 UTC, manual | Updates every testable browser app, Go app, and Rust app; pushes passing updates to `main`, otherwise opens a PR |
| `nypd-choppers-scrape.yml` | hourly, manual | **App-specific:** fetches NYPD helicopter full-day ADS-B traces and merges per-day JSON to `gh-pages` under `nypd-choppers/data/`. Not generalized; shares the `gh-pages-publish` concurrency group with deploy/preview/cleanup |

Deploy workflows copy browser app directories as-is (they do **not** run
`npm install` or build). Go and Rust app directories are not deployed. Only
commit source files—never commit `node_modules/` or Go/Rust build artifacts.

The production home page (`index.html` at the Pages root) is generated at build
time by `.github/scripts/render-index.py` from the shared template. It has a
**Browser apps** section (the deployed `index.html` directories) and a separate
**Cloudflare Workers apps** section (directories with `wrangler.toml`). Workers
are not served from Pages, so the renderer discovers them by scanning the repo
source tree (`--source-dir`, defaulting to the checkout it runs from) and links
each to its source on GitHub. Under the browser apps it lists **active PR
previews** (only browser apps get previews): `preview.yml` writes a
`preview/pr-<N>/preview.json` manifest **only for PRs that change a browser
app** (so Go/Rust/CI-only PRs, whose preview would be identical to production,
are not listed), and `deploy.yml`, `preview.yml`, and `cleanup.yml` each
regenerate the root index from the published `gh-pages` tree so the list stays
current as previews come and go. Because the deploy publishes with
`keep_files: true` (to preserve `preview/`), a browser app that is renamed or
removed in the source tree would otherwise linger on `gh-pages` and keep showing
up on the home page. `deploy.yml` therefore runs
`.github/scripts/prune-orphaned-apps.sh` before regenerating the index to delete
published app directories (those with `index.html`, excluding `preview/`) that
no longer exist as source browser apps. `discover-browser-apps.sh` reports which
browser apps a change set touched; `render-index_test.py` covers the renderer
(run `python3 .github/scripts/render-index_test.py`), and
`prune-orphaned-apps_test.sh` covers the pruner (run
`bash .github/scripts/prune-orphaned-apps_test.sh`).

### Production URLs

- Site root: `https://<owner>.github.io/<repo>/`
- App: `https://<owner>.github.io/<repo>/<app-name>/`
- Example: `https://imjasonh.github.io/playground/kanoodle/`

### PR preview URLs

- Preview root: `https://<owner>.github.io/<repo>/preview/pr-<N>/`
- App: `https://<owner>.github.io/<repo>/preview/pr-<N>/<app-name>/`

The preview workflow posts the preview root URL on the PR.

## Testing (`test.yml`)

Every push to `main` and every pull request runs a single `test` job. It first
discovers which apps changed
(`.github/scripts/discover-changed-apps.sh`), then tests **only the changed apps
of each type**, installing each toolchain (Node, Go, Rust) only when that type
has work to do. When a type has no changes its steps are skipped, so the run is
one `test` check with no empty or skipped legs. On the first push to `main` (no
prior commit), every app is tested.

Discovery is by **top-level directory**: a change under `kanoodle/` selects
`kanoodle`, a change under `web-push/` selects `web-push`, and so on. Hidden
directories (names starting with `.`) and changes outside any app directory
(e.g. a lone top-level file) select nothing — so a PR that only edits CI scripts
or the root `README.md` runs no app tests.

| App type | Selected when its dir has | CI runs, per changed app |
|----------|---------------------------|--------------------------|
| Browser | `index.html` **and** `package.json` with a `test` script | `npm ci` → `npm test` → `npm run test:e2e` (if defined; installs Playwright Chromium first) |
| Go | `go.mod` | `go build ./...` → `go test ./...` |
| Rust | `Cargo.toml` | `cargo fmt --check` → `cargo clippy --locked --all-targets -D warnings` → `cargo test --locked`; Cloudflare Worker apps (with `wrangler.toml`) also run wasm clippy + a release `wasm32-unknown-unknown` build |

Browser apps without a `test` script (e.g. `hello/`) are never tested. Each Rust
app's toolchain comes from its `rust-toolchain.toml` (defaulting to stable);
`web-push` pins Rust 1.83.

Run the per-type discovery helpers locally to see what CI would select:

```bash
# Every app of one type
bash .github/scripts/discover-testable-apps.sh --all   # browser
bash .github/scripts/discover-go-modules.sh --all      # Go
bash .github/scripts/discover-rust-apps.sh --all       # Rust

# Only what a diff touched (what CI uses on a PR)
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-rust-apps.sh --from-changes
```

## Dependency updates (`deps.yaml`)

A scheduled workflow (daily at 00:00 UTC, or on demand via *Run workflow*) keeps
every app's dependencies fresh. For each app it upgrades dependencies with that
ecosystem's idiomatic tool, then verifies the result with the same checks the
test workflow gates on:

| App type | Upgrade | Verify |
|----------|---------|--------|
| Browser | `npx npm-check-updates --upgrade` → `npm install` → `npm run vendor` (if defined) | `npm test` (+ `npm run test:e2e` if defined) |
| Go | `go get -u ./...` | `go build ./...` → `go test ./...` |
| Rust | `cargo update` | `cargo clippy -D warnings` → `cargo test`; Worker apps also wasm clippy + a release `wasm32-unknown-unknown` build |

Publishing is all-or-nothing, so a green run never lands a half-broken bump:

- **Everything upgraded, built, and tested** → it commits the changed
  lockfiles/manifests (`go.mod`/`go.sum`, `package.json`/`package-lock.json`
  plus vendored output, `Cargo.toml`/`Cargo.lock`) straight to `main` as a
  single `chore(deps): update dependencies` commit, and closes any stale
  automation PR.
- **Any upgrade, build, test, or the push fails** → it opens (or updates) a pull
  request on the `automation/dependency-updates` branch with whatever it could
  change — or an empty commit when nothing did — so a human can finish the
  upgrade, and the run is marked failed.

Each ecosystem's work lives in its own script (`update-go-dependencies.sh`,
`update-js-dependencies.sh`, `update-rust-dependencies.sh`), and
`manage-dependency-update.sh` performs the shared commit / PR / report step. New
apps are discovered automatically — no workflow edits are needed.

## Adding a new browser app

1. Create a **top-level directory** (e.g. `my-app/`).
2. Add **`my-app/index.html`** as the entry point.
3. Keep all assets inside that directory (CSS, JS, images).
4. Optional but recommended for non-trivial apps:
   - Add `my-app/package.json` with `"test"` script
   - Add `my-app/README.md` with run/test instructions
   - Add `my-app/.gitignore` (at minimum `node_modules/`)
5. Open a PR—preview deploy and CI run automatically.

No workflow edits are required when a new app follows these conventions.

### Minimal static app

```
my-app/
└── index.html
```

Serve locally: `npx serve my-app` or open `index.html` in a browser.

### App with tests (recommended pattern)

Follow `kanoodle/` as a reference:

```
my-app/
├── index.html
├── package.json       # scripts: test, optionally test:e2e, start
├── package-lock.json  # commit lockfile for reproducible CI
├── .gitignore
├── src/               # ES modules or bundled source
├── tests/             # unit tests (e.g. Jest)
└── e2e/               # optional browser tests (e.g. Playwright)
```

Run locally:

```bash
cd my-app
npm install
npm test
npm run test:e2e   # if defined
npm start          # if defined (static server)
```

## Adding a new Go app

1. Create a **top-level directory** (for example, `my-tool/`).
2. Initialize an independent module at `my-tool/go.mod`.
3. Keep all Go sources and tests inside that directory.
4. Commit `go.sum` when the module has dependencies.
5. Add `my-tool/README.md` with build, run, and test instructions.
6. Add `my-tool/.gitignore` for local binaries and other generated output.
7. Do **not** add `index.html`; Go apps are not deployed or previewed.

No workflow edits are required. CI discovers a new Go app from its `go.mod`,
and the daily dependency workflow includes it automatically.

Run locally:

```bash
cd my-tool
go build ./...
go test ./...
```

## Adding a new Rust app

1. Create a **top-level directory** (for example, `my-worker/`).
2. Initialize an independent crate at `my-worker/Cargo.toml` and commit
   `Cargo.lock`.
3. Keep all Rust sources and tests inside that directory.
4. Add `my-worker/rust-toolchain.toml` pinning the toolchain (and, for a
   Cloudflare Worker, the `wasm32-unknown-unknown` target).
5. Add `my-worker/README.md` and a `my-worker/.gitignore` (at least `target/`).
6. Do **not** add `index.html`; Rust apps are not served from Pages or
   previewed. If you want a UI, add a separate browser app (see `web-push-demo`).
7. For a Cloudflare Worker, add a `wrangler.toml`. `deploy-workers.yml` then
   deploys it on pushes to `main` automatically (no workflow edits needed); it
   relies on the `CLOUDFLARE_API_TOKEN` and `CLOUDFLARE_ACCOUNT_ID` repo secrets.
   The deploy self-provisions Cloudflare-side config: KV namespaces referenced
   with a placeholder id (e.g. `id = "REPLACE_WITH_..."`) are created-or-fetched
   and rewritten to real ids before deploy, and a Worker that ships
   `examples/genvapid.rs` gets a `VAPID_PRIVATE_KEY` secret generated once (only
   if absent, so the key is stable across deploys).

No workflow edits are required. CI discovers a new Rust app from its
`Cargo.toml`, the deploy workflow discovers a new Worker from its
`wrangler.toml`, and the daily dependency workflow includes it automatically.

Run locally:

```bash
cd my-worker
cargo fmt --check
cargo clippy --all-targets
cargo test
```

## Implementation conventions

- **Browser apps are client-side**: they must be static sites suitable for GitHub Pages (no server-side runtime in production).
- **Prefer plain HTML + JS** for browser apps unless an app already uses a framework; match the style of neighboring code in that app directory.
- **Go apps are independent modules**: each app owns its `go.mod` and `go.sum`; avoid cross-app imports.
- **Rust apps are independent crates**: each app owns its `Cargo.toml`, `Cargo.lock`, and `rust-toolchain.toml`; avoid cross-app imports.
- **Keep all apps isolated**: do not add repo-root `package.json`, `go.mod`, `go.work`, or Cargo workspace files unless the maintainers explicitly request a monorepo toolchain.
- **Minimize scope**: when fixing or extending one app, avoid unrelated changes in other directories.
- **Do not commit**: `node_modules/`, secrets, env files, browser/Go/Rust build artifacts (`target/`), or Playwright/Jest output (`test-results/`, `coverage/`).

## Pull requests

- Target branch: **`main`**
- **No stacked PRs — branch every PR off `main`.** Each PR must be
  independently mergeable on its own, in any order. Do **not** base one PR's
  branch on another PR's branch (or on any non-`main` branch). Stacking has
  bitten this repo: when the base PR merges first and its branch lingers, a
  later merge of the "stacked" PR lands in that now-stale branch instead of
  `main`, so the work silently never reaches `main` and is easily lost. If two
  changes are related, either keep them in separate `main`-based PRs that don't
  touch the same lines, or combine them into a single PR — never stack.
- **Treat merged PRs as immutable.** Once a PR is merged, don't push more
  commits to its branch, reopen it, or amend it. Make any follow-up change
  (fix, revert, addition) in a **new** PR branched off `main`.
- CI must pass (changed browser apps are tested; changed Go and Rust apps are built and tested).
- Preview deploy provides a live URL for browser apps only—use it to verify browser behavior, especially mobile.
- If the repo uses Linear integration, include `Resolves ABC-123` in the PR body when applicable.

## Current browser apps

| Directory | Type | Tests |
|-----------|------|-------|
| `artillery/` | Turn-based artillery duel with local and AI modes | Node test runner |
| `cold-climb/` | Two-handle ball-climbing arcade game | Node test runner |
| `cors-proxy-demo/` | Browser playground for the `cors-proxy` Worker (send a request, inspect the CORS response) | none (static) |
| `git/` | In-browser read-only git client (clone, browse, branches, history) | Jest + Playwright |
| `hello/` | Static demo | none |
| `kanoodle/` | Kanoodle puzzle game (5×11 board, 12 pieces) | Jest + Playwright |
| `nypd-choppers/` | NYPD helicopter daily flight paths, hours, and fuel-cost estimates from ADS-B | Node test runner |
| `web-push-demo/` | Browser front-end for `web-push` (subscribe/unsubscribe/notify) | none (static) |

> **`nypd-choppers` has an intentionally non-standard lifecycle.** Because free
> ADS-B APIs are blocked by CORS and only serve live (current-position) data, it
> relies on the hourly `nypd-choppers-scrape.yml` workflow to fetch full-day
> flight traces and accumulate historical data, which it commits to the
> `gh-pages` branch (never `main`). Do not try to fold this data-collection
> pattern into the shared deploy/test/deps workflows.

## Current Go apps

| Directory | Type | Tests |
|-----------|------|-------|
| `gitdb/` | git repository explorer backed by SQLite virtual tables | `go test ./...` |
| `ocidb/` | OCI registry explorer backed by SQLite virtual tables | `go test ./...` |

## Current Rust apps

| Directory | Type | Tests |
|-----------|------|-------|
| `web-push/` | Web Push backend — Cloudflare Worker (RFC 8030/8188/8291/8292) | `cargo test` + clippy + wasm build |
| `cors-proxy/` | SSRF-hardened CORS proxy — Cloudflare Worker | `cargo test` + clippy + wasm build |

See each app's `README.md` for app-specific rules and local development.
