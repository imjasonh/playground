# Agent guide: playground

This repository is a **multi-app playground**. Each top-level directory can be
either a self-contained browser app deployed to GitHub Pages or an independent
Go command-line app. There is no shared build step at the repo root.

## Repository layout

```
playground/
├── AGENTS.md              ← you are here
├── README.md
├── .github/
│   ├── pages/             # shared HTML template for app index pages
│   ├── scripts/           # CI helpers for browser and Go app discovery
│   └── workflows/         # deploy, preview, test, cleanup, dependency updates
├── git/                   # in-browser read-only git client (JS + Jest + Playwright)
├── gitdb/                 # Go CLI (Go module + Go tests)
├── hello/                 # example static app (HTML only)
├── kanoodle/              # example app with tests (JS + Jest + Playwright)
└── ocidb/                 # Go CLI (Go module + Go tests)
```

### Browser apps

A top-level directory is a **browser app** when it contains **`index.html`** at
its root. This is the same rule used by deploy and preview workflows.

| Path | Browser app? | Notes |
|------|--------------|-------|
| `git/` | yes | In-browser read-only git client; JS modules, npm scripts, tests |
| `hello/` | yes | Static HTML; no build or tests |
| `kanoodle/` | yes | Client-side JS modules, npm scripts, tests |
| `gitdb/` | no | Go CLI; no `index.html` |
| `ocidb/` | no | Go CLI; no `index.html` |
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

Hidden top-level directories (names starting with `.`) are ignored by all app
discovery scripts.

## GitHub Actions

| Workflow | Trigger | Purpose |
|----------|---------|---------|
| `deploy.yml` | push to `main` | Publishes all browser apps to GitHub Pages production |
| `preview.yml` | pull request opened/sync | Deploys browser apps under `/preview/pr-<N>/` and comments the URL |
| `cleanup.yml` | pull request closed | Removes that PR's preview directory from `gh-pages` |
| `test.yml` | push to `main`, pull requests | Tests changed browser apps and fans out build/test jobs for changed Go apps |
| `deps.yaml` | daily at 00:00 UTC, manual | Updates every Go app's dependencies; pushes passing updates to `main`, otherwise opens a PR |

Deploy workflows copy browser app directories as-is (they do **not** run
`npm install` or build). Go app directories are not deployed. Only commit
source files—never commit `node_modules/` or Go build artifacts.

### Production URLs

- Site root: `https://<owner>.github.io/<repo>/`
- App: `https://<owner>.github.io/<repo>/<app-name>/`
- Example: `https://imjasonh.github.io/playground/kanoodle/`

### PR preview URLs

- Preview root: `https://<owner>.github.io/<repo>/preview/pr-<N>/`
- App: `https://<owner>.github.io/<repo>/preview/pr-<N>/<app-name>/`

The preview workflow posts the preview root URL on the PR.

## Testing browser apps (CI)

The browser test job tests only the **testable browser apps whose top-level
directory changed** in the PR or push. Unchanged browser apps are not tested.
The job always runs, discovering changed testable apps and testing them in
turn; it exits green with a "Nothing to test" message when none changed.

A browser app is testable when it has:

1. `index.html` (is a browser app)
2. `package.json` with a **`test`** script

Apps without tests (e.g. `hello/`) are not tested. If no testable apps changed, the `test` job still runs and passes without running any app tests.

For each selected app, CI runs:

1. `npm ci`
2. `npm test`
3. `npm run test:e2e` if a `test:e2e` script exists (installs Playwright Chromium first)

On the first push to `main` (no prior commit), all testable apps are tested.

## Testing Go apps (CI)

The test workflow discovers changed Go apps independently of browser apps and
fans them out into one job per module. For every selected module, CI runs:

1. `go build ./...`
2. `go test ./...`

Changing any path under a Go app selects that module. Adding a top-level
`<name>/go.mod` selects the new app. Changes to the Go discovery script or the
Go CI workflow test every Go app so CI infrastructure changes exercise the
full fan-out. On the first push to `main`, every Go app is tested.

The daily dependency workflow runs `go get -u ./...`, `go build ./...`, and
`go test ./...` in every Go app module. It commits passing dependency changes
directly to `main`. If updating, building, testing, or pushing fails, it puts
the changes (or an empty failure-report commit) on a pull request instead.

Discover apps locally:

```bash
# All testable browser apps
bash .github/scripts/discover-testable-apps.sh --all

# Browser apps touched by a diff
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-testable-apps.sh --from-changes

# All Go apps
bash .github/scripts/discover-go-modules.sh --all

# Go apps touched by a diff
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-go-modules.sh --from-changes
```

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

## Implementation conventions

- **Browser apps are client-side**: they must be static sites suitable for GitHub Pages (no server-side runtime in production).
- **Prefer plain HTML + JS** for browser apps unless an app already uses a framework; match the style of neighboring code in that app directory.
- **Go apps are independent modules**: each app owns its `go.mod` and `go.sum`; avoid cross-app imports.
- **Keep all apps isolated**: do not add repo-root `package.json`, `go.mod`, or `go.work` files unless the maintainers explicitly request a monorepo toolchain.
- **Minimize scope**: when fixing or extending one app, avoid unrelated changes in other directories.
- **Do not commit**: `node_modules/`, secrets, env files, browser or Go build artifacts, or Playwright/Jest output (`test-results/`, `coverage/`).

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
- CI must pass (changed browser apps are tested; changed Go apps are built and tested).
- Preview deploy provides a live URL for browser apps only—use it to verify browser behavior, especially mobile.
- If the repo uses Linear integration, include `Resolves ABC-123` in the PR body when applicable.

## Current browser apps

| Directory | Type | Tests |
|-----------|------|-------|
| `git/` | In-browser read-only git client (clone, browse, branches, history) | Jest + Playwright |
| `hello/` | Static demo | none |
| `kanoodle/` | Kanoodle puzzle game (5×11 board, 12 pieces) | Jest + Playwright |

## Current Go apps

| Directory | Type | Tests |
|-----------|------|-------|
| `gitdb/` | git repository explorer backed by SQLite virtual tables | `go test ./...` |
| `ocidb/` | OCI registry explorer backed by SQLite virtual tables | `go test ./...` |

See each app's `README.md` for app-specific rules and local development.
