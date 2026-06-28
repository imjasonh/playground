# Agent guide: playground

This repository is a **multi-app playground**: each top-level directory can be a self-contained browser app deployed to GitHub Pages. There is no shared build step at the repo root—apps are independent.

## Repository layout

```
playground/
├── AGENTS.md              ← you are here
├── README.md
├── .github/
│   ├── pages/             # shared HTML template for app index pages
│   ├── scripts/           # CI helpers (e.g. discover testable apps)
│   └── workflows/         # deploy, preview, test, cleanup
├── git/                   # in-browser read-only git client (JS + Jest + Playwright)
├── hello/                 # example static app (HTML only)
└── kanoodle/              # example app with tests (JS + Jest + Playwright)
```

### What counts as an app

A directory is an **app** when it contains **`index.html`** at its root. This is the same rule used by deploy and preview workflows.

| Path | App? | Notes |
|------|------|-------|
| `git/` | yes | In-browser read-only git client; JS modules, npm scripts, tests |
| `hello/` | yes | Static HTML; no build or tests |
| `kanoodle/` | yes | Client-side JS modules, npm scripts, tests |
| `.github/` | no | Infrastructure only |
| `README.md` | no | Not a directory |

Hidden top-level directories (names starting with `.`) are ignored by discovery scripts.

## GitHub Actions

| Workflow | Trigger | Purpose |
|----------|---------|---------|
| `deploy.yml` | push to `main` | Publishes all apps to GitHub Pages production |
| `preview.yml` | pull request opened/sync | Deploys PR apps under `/preview/pr-<N>/` and comments the URL |
| `cleanup.yml` | pull request closed | Removes that PR's preview directory from `gh-pages` |
| `test.yml` | push to `main`, pull requests | Runs tests for **changed** testable apps only (matrix) |

All deploy workflows copy each app directory as-is (they do **not** run `npm install` or build). Only commit source files—never commit `node_modules/`.

### Production URLs

- Site root: `https://<owner>.github.io/<repo>/`
- App: `https://<owner>.github.io/<repo>/<app-name>/`
- Example: `https://imjasonh.github.io/playground/kanoodle/`

### PR preview URLs

- Preview root: `https://<owner>.github.io/<repo>/preview/pr-<N>/`
- App: `https://<owner>.github.io/<repo>/preview/pr-<N>/<app-name>/`

The preview workflow posts the preview root URL on the PR.

## Testing (CI)

The test workflow runs only for **testable apps whose top-level directory changed** in the PR or push. Unchanged apps are not tested.

An app is testable when it has:

1. `index.html` (is an app)
2. `package.json` with a **`test`** script

Apps without tests (e.g. `hello/`) are skipped. If no testable apps changed, CI passes without running tests.

For each selected app, CI runs:

1. `npm ci`
2. `npm test`
3. `npm run test:e2e` if a `test:e2e` script exists (installs Playwright Chromium first)

On the first push to `main` (no prior commit), all testable apps are tested.

Discover locally:

```bash
# All testable apps
bash .github/scripts/discover-testable-apps.sh --all

# Apps touched by a diff (example)
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-testable-apps.sh --from-changes
```

## Adding a new app

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

## Implementation conventions

- **Client-side first**: apps are static sites suitable for GitHub Pages (no server-side runtime in production).
- **Prefer plain HTML + JS** unless an app already uses a framework; match the style of neighboring code in that app directory.
- **Keep apps isolated**: do not add cross-app imports or a repo-root `package.json` unless the maintainers explicitly request a monorepo toolchain.
- **Minimize scope**: when fixing or extending one app, avoid unrelated changes in other directories.
- **Do not commit**: `node_modules/`, secrets, env files, build artifacts, or Playwright/Jest output (`test-results/`, `coverage/`).

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
- CI must pass (tests run for **changed** testable apps in that PR).
- Preview deploy provides a live URL on the PR—use it to verify browser behavior, especially mobile.
- If the repo uses Linear integration, include `Resolves ABC-123` in the PR body when applicable.

## Current apps

| Directory | Type | Tests |
|-----------|------|-------|
| `git/` | In-browser read-only git client (clone, browse, branches, history) | Jest + Playwright |
| `hello/` | Static demo | none |
| `kanoodle/` | Kanoodle puzzle game (5×11 board, 12 pieces) | Jest + Playwright |

See each app's `README.md` for game-specific rules and local development.
