# Agent guide: playground

This repository is a **multi-app playground**. Each top-level directory can be a
browser app on GitHub Pages, a Go CLI, a Rust app (for example a Cloudflare
Worker), an iOS app on TestFlight, or a macOS app signed with Developer ID and
shipped through Sparkle. There is no shared build step at the repo root.

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
├── chessh/                # multiplayer chess over SSH (Go + Terraform)
├── cold-climb/            # touch-first two-handle arcade game (JS + Node tests)
├── droneski/              # FPV drone filming a downhill skier (JS + three.js + Node tests)
├── esp-flash/             # Web Serial / WebUSB ESP32 flasher (inkbot GHCR + local .bin)
├── kubescheduler-the-game/ # Kubernetes scheduler + cluster-operator game (JS + Node tests)
├── cors-proxy/            # Rust Cloudflare Worker: SSRF-hardened CORS proxy (not a Pages app)
├── cors-proxy-demo/       # static browser front-end for the cors-proxy Worker
├── git/                   # in-browser read-only git client (JS + Jest + Playwright)
├── git-fuse/              # Rust CLI: read-only FUSE adapter for git-server (not a Pages app)
├── git-server/            # Rust Cloudflare Worker: git smart-HTTP server on R2/DO (not a Pages app)
├── life-lab/              # browser front-end for life-stl (wasm + three.js + Node tests)
├── its-not-jaws/          # Cursor SDK harness: knower/guesser secret-guessing game
├── life-qr/               # OpenSCAD Life sculpture with a QR-code roof (parametric)
├── life-scad/             # OpenSCAD Life sculpture + reverse-history Python tool
├── life-stl/              # Rust CLI: Game of Life → printable STL (Z = time)
├── mapvelopes/            # Rust Cloudflare Worker: envelope PDFs with a route map
├── gitdb/                 # Go CLI (Go module + Go tests)
├── hello/                 # example static app (HTML only)
├── hello-macos/           # example macOS SwiftUI app (XcodeGen + Sparkle CD)
├── onramp/             # offline Mac can’t-get-online triage (Sparkle CD)
├── inkbot/                # Rust Cloudflare Worker: e-ink frame host + Slack @inkbot
├── inkbot-esp32/          # Rust/ESP-IDF firmware: poll inkbot + signed OTA, or APP=maze, on Waveshare 7.5″
├── ios/                   # the single "Playground" iOS app (SwiftUI; TestFlight CD)
├── kanoodle/              # example app with tests (JS + Jest + Playwright)
├── nypd-choppers/         # NYPD helicopter ADS-B tracker (JS + Node tests)
├── ocidb/                 # Go CLI (Go module + Go tests)
├── pasta/                 # CUE + tree-sitter multi-language linters/fixers (Go CLI)
├── population-rays/       # directional 5° population-slice map (JS + Node tests)
├── web-push/              # Rust Cloudflare Worker (Cargo + tests; not a Pages app)
├── web-push-demo/         # static browser front-end for the web-push Worker
└── y/                     # Rust Cloudflare Worker: one-user microblog
```

### Browser apps

A top-level directory is a **browser app** when it contains **`index.html`** at
its root. This is the same rule used by deploy and preview workflows.

| Path | Browser app? | Notes |
|------|--------------|-------|
| `artillery/` | yes | Turn-based artillery duel; JS modules, npm scripts, tests |
| `cold-climb/` | yes | Touch-first arcade game; JS modules, npm scripts, tests |
| `droneski/` | yes | FPV drone / downhill skier game; JS modules, vendored three.js, tests |
| `esp-flash/` | yes | Web Serial / WebUSB ESP32 flasher; JS modules, vendored esptool-js, tests |
| `kubescheduler-the-game/` | yes | Kubernetes scheduler game; JS modules, npm scripts, tests |
| `cors-proxy-demo/` | yes | Static front-end for `cors-proxy`; HTML/JS, no build or tests |
| `git/` | yes | In-browser read-only git client; JS modules, npm scripts, tests |
| `hello/` | yes | Static HTML; no build or tests |
| `kanoodle/` | yes | Client-side JS modules, npm scripts, tests |
| `life-lab/` | yes | Game of Life sculpture lab; vendored wasm built from `life-stl/` |
| `nypd-choppers/` | yes | NYPD helicopter tracker; JS modules, npm scripts, tests |
| `population-rays/` | yes | Directional 5° population slices; JS modules, npm scripts, tests |
| `web-push-demo/` | yes | Static front-end for `web-push`; HTML/JS, no build or tests |
| `chessh/` | no | Go SSH chess server on exe.dev; no `index.html` |
| `gitdb/` | no | Go CLI; no `index.html` |
| `ocidb/` | no | Go CLI; no `index.html` |
| `pasta/` | no | Go CLI (CUE + tree-sitter linters); no `index.html` |
| `web-push/` | no | Rust Cloudflare Worker; no `index.html` |
| `y/` | no | Rust Cloudflare Worker (one-user microblog); no `index.html` |
| `cors-proxy/` | no | Rust Cloudflare Worker; no `index.html` |
| `inkbot/` | no | Rust Cloudflare Worker (e-ink frame + Slack); no `index.html` |
| `inkbot-esp32/` | no | Rust/ESP-IDF ESP32 firmware (espup); no `index.html` |
| `git-server/` | no | Rust Cloudflare Worker; no `index.html` |
| `git-fuse/` | no | Rust CLI (FUSE); no `index.html` |
| `life-stl/` | no | Rust CLI (STL generator); no `index.html` |
| `mapvelopes/` | no | Rust Cloudflare Worker; no `index.html` |
| `its-not-jaws/` | no | Cursor SDK knower/guesser guessing harness; no `index.html` |
| `life-scad/` | no | OpenSCAD + Python reverse-history tool; no `index.html` |
| `life-qr/` | no | OpenSCAD Life+QR sculpture; no `index.html` |
| `ios/` | no | The single "Playground" iOS app (XcodeGen + SwiftUI); no `index.html` |
| `hello-macos/` | no | Example macOS app (XcodeGen + SwiftUI); no `index.html` |
| `onramp/` | no | Offline Mac network triage / can’t-get-online playbooks (XcodeGen + SwiftUI + Sparkle); no `index.html` |
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

### iOS apps

Unlike browser/Go/Rust apps, there is exactly **one** iOS app: the **Playground**
app in **`ios/`** (marker: **`project.yml`**, an
[XcodeGen](https://github.com/yonaskolb/XcodeGen) spec that is the single source
of truth for the Xcode project). This mirrors the way the Pages site is one site
hosting many browser apps: the one TestFlight app hosts many **experiments**
internally. **Do not create additional top-level iOS app directories** — add an
experiment inside `ios/` instead (see "Adding an experiment to the iOS app").
The generated `*.xcodeproj` is git-ignored and regenerated in CI.

The iOS app is **not** a browser app: it has no `index.html`. It is built and
tested on a macOS runner and, on push to `main`, delivered to **TestFlight**; it
is not copied to GitHub Pages and (today) does not receive PR preview installs —
the `ios.yml` workflow tests it on PRs but only ships from `main`.

The app owns its `project.yml`, `fastlane/`, and single bundle identifier
(`io.github.imjasonh.playground`); do not add a repo-root Xcode workspace. Do not
commit build artifacts (`*.xcodeproj`, `DerivedData/`, `*.ipa`, `*.xcarchive`)
or any signing material (`*.p8`, `*.p12`, `*.mobileprovision`). TestFlight
delivery requires Apple credentials configured as repo secrets; without them CI
still runs the tests and skips the upload. See
[`docs/ios-testflight-design.md`](docs/ios-testflight-design.md) for the design
and [`docs/ios-testflight-setup.md`](docs/ios-testflight-setup.md) for a
click-by-click Apple-side setup guide. The iOS app is not yet covered by the
daily dependency workflow.

### macOS apps

A top-level directory is a **macOS app** when it contains **`project.yml`**
(XcodeGen) that declares at least one target with **`platform: macOS`**. iOS
apps also use `project.yml` but declare `platform: iOS` — discovery scripts
distinguish the two by that line. Unlike iOS (exactly one Playground host),
**many macOS apps are allowed**, each in its own top-level directory with its
own Bundle ID. Do **not** add macOS apps under `ios/`, and do **not** add
`index.html` (they are not Pages browser apps).

macOS apps are built and tested by `macos.yml` on a macOS runner. On push to
`main` with Developer ID / Sparkle secrets present, CI notarizes and publishes
a Sparkle appcast (see [`docs/macos-sparkle-design.md`](docs/macos-sparkle-design.md)
and [`docs/macos-sparkle-setup.md`](docs/macos-sparkle-setup.md)); without those
secrets, CI still runs tests and skips the release. Do not commit `*.xcodeproj`,
`DerivedData/`, `*.dmg`, `*.xcarchive`, or signing material.

Hidden top-level directories (names starting with `.`) are ignored by all app
discovery scripts.

## GitHub Actions

| Workflow | Trigger | Purpose |
|----------|---------|---------|
| `deploy.yml` | push to `main` | Publishes all browser apps to GitHub Pages production |
| `deploy-workers.yml` | push to `main`, manual | Deploys changed Cloudflare Worker apps (those with `wrangler.toml`) with `wrangler`, using the `CLOUDFLARE_API_TOKEN` and `CLOUDFLARE_ACCOUNT_ID` repo secrets; a manual *Run workflow* (`workflow_dispatch`) redeploys all of them. Before deploy it create-or-gets each Worker's KV namespaces (substituting the placeholder ids in `wrangler.toml`), creates any declared R2 buckets that don't exist, and applies remote D1 migrations for declared `[[d1_databases]]`; after deploy it get-or-generates a `VAPID_PRIVATE_KEY` secret for any Worker shipping an `examples/genvapid.rs` |
| `deploy-exe.yml` | push to `main`, manual | Deploys changed [exe.dev](https://exe.dev) apps (top-level dirs whose `iac/` declares the `benjamin-lykins/exedev` Terraform provider). Uses `ko_build` to push images to GHCR, applies Terraform with state in Cloudflare R2 (`playground-terraform-state`), and authenticates to exe.dev by minting `EXEDEV_TOKEN` from the `EXEDEV_SSH_PRIVATE_KEY` secret. Terraform talks to R2 with short-lived S3 credentials minted from the existing `CLOUDFLARE_API_TOKEN` (bucket create uses the same token). Manual dispatch redeploys every exe app. |
| `preview.yml` | pull request opened/sync | When a browser app, the posts catalog, or the Pages home-page index changed: deploys under `/preview/pr-<N>/` and comments the URL; otherwise no-ops |
| `cleanup.yml` | pull request closed, manual | Removes closed-PR preview dirs from `gh-pages` (reconciles all open PRs) and refreshes the root index |
| `test.yml` | push to `main`, pull requests | Tests changed browser, Go, and Rust apps, plus the pasta style leg, posts catalog, and site index, in one job |
| `inkbot-esp32.yml` | push to `main`, pull requests, manual | Always runs discover + host/firmware jobs (so they can be required checks); host/firmware no-op when `inkbot-esp32/` (or this workflow) is unchanged (excluded from `test.yml`) |
| `inkbot-esp32-publish.yml` | push to `main` touching `inkbot-esp32/**` (or this workflow), manual | Cross-builds inkbot firmware, pushes `ghcr.io/<owner>/playground/inkbot-esp32`, and Cosign-signs the digest (devices poll this for OTA) |
| `ios.yml` | push to `main`, pull requests | Tests changed iOS apps on macOS; on `main`, delivers them to TestFlight |
| `macos.yml` | push to `main`, pull requests | Tests changed macOS apps on macOS; on `main`, ships notarized Sparkle updates when secrets are present |
| `ios-bootstrap-label.yml` | pull request | Labels PRs that need signing re-bootstrap with `needs-ios-bootstrap` |
| `ios-bootstrap-on-merge.yml` | pull request closed (merged) | If the PR had `needs-ios-bootstrap`, immediately re-runs signing bootstrap (races `ios.yml`; usually finishes first) |
| `ios-signing-bootstrap.yml` | manual (`workflow_dispatch`) + reusable | Creates & stores signing cert/profile in the `match` repo; also called on labeled merges |
| `deps.yaml` | daily at 00:00 UTC, manual | Updates every testable browser app, Go app, and Rust app; opens a PR and auto-merges passing updates to `main`, otherwise leaves a PR for review |
| `nypd-choppers-scrape.yml` | hourly, manual | **App-specific:** fetches NYPD helicopter full-day ADS-B traces and merges per-day JSON to `gh-pages` under `nypd-choppers/data/`. Not generalized; shares the `gh-pages-publish` concurrency group with deploy/preview/cleanup |
| `its-not-jaws.yml` | pull requests touching `its-not-jaws/**`, manual | **App-specific:** requires repo secret `CURSOR_API_KEY` (fails if missing), unit-tests the harness, plays one live Cursor Agent SDK game, uploads the result artifact |

Deploy workflows copy browser app directories as-is (they do **not** run
`npm install` or build). Go and Rust app directories are not deployed. Only
commit source files—never commit `node_modules/` or Go/Rust build artifacts.

The production home page (`index.html` at the Pages root) is generated at build
time by `.github/scripts/render-index.py` from the shared template. The header
links to the generated **Posts** catalog (`posts/`). The page then lists a
**Browser apps** section (the deployed `index.html` directories) and a separate
**Cloudflare Workers apps** section (directories with `wrangler.toml`). Workers
are not served from Pages, so the renderer discovers them by scanning the repo
source tree (`--source-dir`, defaulting to the checkout it runs from) and links
each to its deployed Worker at
`https://<wrangler-name>.imjasonh.workers.dev` (the top-level `name` in that
app's `wrangler.toml`). Under the browser apps it lists **active PR
previews**: `preview.yml` discovers changed browser apps, posts-catalog
files, and the Pages home-page index first and **skips deploy + PR comment**
when none of those changed (so Go/Rust/iOS/CI-only PRs, whose preview would be
identical to production, stay quiet). If any of those changed, it writes
`preview/pr-<N>/preview.json` and comments the URL. The preview directory is
built from the PR. The production home page is regenerated with the PR base
branch's index template, so an unmerged template change does not go live.
`deploy.yml` also runs
`.github/scripts/build-blog.py` to publish `/posts/` from every `blog-post.md`
in the source tree. `deploy.yml`, `preview.yml`, and `cleanup.yml` each
regenerate the root index from the published `gh-pages` tree so the list stays
current as previews come and go. Because the deploy publishes with
`keep_files: true` (to preserve `preview/`), a browser app that is renamed or
removed in the source tree would otherwise linger on `gh-pages` and keep showing
up on the home page. `deploy.yml` therefore runs
`.github/scripts/prune-orphaned-apps.sh` before regenerating the index to delete
published app directories (those with `index.html`, excluding `preview/` and
the generated `posts/` catalog) that
no longer exist as source browser apps. The same `keep_files: true` setting also
preserves `preview/pr-<N>/` directories; `cleanup.yml` removes one on close, but
bulk-closing PRs can drop some `pull_request` closed webhooks, leaving closed
previews listed on the home page. Both `cleanup.yml` and `deploy.yml` therefore
also run `.github/scripts/prune-orphaned-previews.sh`, which deletes every
`preview/pr-<N>/` whose PR is not currently open (and `cleanup.yml` supports
`workflow_dispatch` for a manual reconcile). `discover-browser-apps.sh` reports
which browser apps a change set touched; `render-index_test.py` covers the
renderer (run `python3 .github/scripts/render-index_test.py`),
`discover-index_test.sh` covers when the site-index preview/CI leg runs (run
`bash .github/scripts/discover-index_test.sh`),
`prune-orphaned-apps_test.sh` covers the app pruner (run
`bash .github/scripts/prune-orphaned-apps_test.sh`), and
`prune-orphaned-previews_test.sh` covers the preview pruner (run
`bash .github/scripts/prune-orphaned-previews_test.sh`). The posts catalog
builder is covered by `python3 .github/scripts/build-blog_test.py`.

### Production URLs

- Site root: `https://<owner>.github.io/<repo>/`
- App: `https://<owner>.github.io/<repo>/<app-name>/`
- Posts: `https://<owner>.github.io/<repo>/posts/`
- Posts RSS: `https://<owner>.github.io/<repo>/posts/feed.xml`
- Example: `https://imjasonh.github.io/playground/kanoodle/`
- Worker: `https://<wrangler-name>.imjasonh.workers.dev` (for example
  `https://y.imjasonh.workers.dev`)

### PR preview URLs

- Preview root: `https://<owner>.github.io/<repo>/preview/pr-<N>/`
- App: `https://<owner>.github.io/<repo>/preview/pr-<N>/<app-name>/`
- Posts: `https://<owner>.github.io/<repo>/preview/pr-<N>/posts/`
- Posts RSS: `https://<owner>.github.io/<repo>/preview/pr-<N>/posts/feed.xml`

The preview workflow posts the preview root URL on the PR when the PR
changes a browser app, the posts catalog, or the Pages home-page index (same
condition as writing `preview.json`); other Go/Rust/iOS/CI-only PRs get
neither a deploy nor a comment.

## Testing (`test.yml`)

Every push to `main` and every pull request runs a single `test` job. It first
discovers which apps changed
(`.github/scripts/discover-changed-apps.sh`), then tests **only the changed apps
of each type**, installing each toolchain (Node, Go, Rust) only when that type
has work to do and running the browser / Go / Rust / pasta / posts / site-index test legs concurrently via
an Actions `parallel:` step group (same pattern as `deps.yaml`). When a type has
no changes its steps are skipped, so the run is one `test` check with no empty
or skipped legs. On the first push to `main` (no prior commit), every app is
tested. The **pasta** leg builds the `pasta/` CLI, runs `pasta test` over the
enrolled `.pasta/` analyzers, and lints the monorepo with `-fail-on=warning`
(see `.github/scripts/test-pasta.sh`).

Discovery is by **top-level directory**: a change under `kanoodle/` selects
`kanoodle`, a change under `web-push/` selects `web-push`, and so on. Hidden
directories (names starting with `.`) and changes outside any app directory
(e.g. a lone top-level file) select nothing — so a PR that only edits CI scripts
or the root `README.md` runs no app tests. `inkbot-esp32/` has a `Cargo.toml`
but is excluded from Rust discovery because it needs the espup Xtensa toolchain;
`inkbot-esp32.yml` runs its host lib tests and firmware cross-build instead.

| App type | Selected when its dir has | CI runs, per changed app |
|----------|---------------------------|--------------------------|
| Browser | `index.html` **and** `package.json` with a `test` script | `npm ci` → `npm test` → `npm run test:e2e` (if defined; installs Playwright Chromium first) |
| Go | `go.mod` | `go build ./...` → `go test -race ./...` |
| Rust | `Cargo.toml` | `cargo fmt --check` → `cargo clippy --locked --all-targets -D warnings` → `cargo test --locked`; Cloudflare Worker apps (with `wrangler.toml`) also run wasm clippy + a release `wasm32-unknown-unknown` build, then the wrangler `[build]` command (with a decoy `package.json` like wrangler-action creates) so Test covers the deploy artifact path. Crates set `[lints.rust] unused = "deny"` so unused methods fail even without clippy. |
| pasta | `pasta/` / `.pasta/` / lintable sources (`.go`, `.js`, `.ts`, `.tsx`, `.jsx`, `.rs`, `.swift`, `.sh`, `.yml`, `.yaml`, `.html`, `.css`, `.toml`, `.tf`, `.tfvars`, `.hcl`, …) via `discover-pasta.sh` | `go build ./pasta/cmd/pasta` → `pasta test .pasta` → `pasta -fail-on=warning ./...` |
| posts | any `blog-post.md`, or `.github/scripts/build-blog*` / `test-blog.sh` / `discover-blog.sh` / the blog page templates, via `discover-blog.sh` | `python3 .github/scripts/build-blog_test.py` |
| site index | `.github/pages/index.html.tmpl`, `render-index.py`, `publish-site-index.sh`, or the index discovery/test scripts, via `discover-index.sh` | `python3 .github/scripts/render-index_test.py` and `bash .github/scripts/discover-index_test.sh` |

Go is the only ecosystem here with a stable, first-class data-race detector (`go test -race`). Rust ThreadSanitizer is still nightly-only and cannot instrument `wasm32-unknown-unknown` Worker tests; JavaScript/Node has no equivalent flag. Those legs stay as they are.

Browser apps without a `test` script (e.g. `hello/`) are never tested. Each Rust
app's toolchain comes from its `rust-toolchain.toml` (defaulting to stable);
Worker apps pin Rust 1.88 (with `worker` 0.8 / wasm-bindgen 0.2.125).

**ESP32 firmware is tested by `inkbot-esp32.yml`, not `test.yml`.** Stable
Linux Cargo cannot build `xtensa-esp32-espidf`; the dedicated workflow installs
the esp-rs Xtensa toolchain, runs host `cargo test --lib` / clippy / provision
dry-run, and `make build`s both the inkbot and maze device images when
`inkbot-esp32/` changes. Signed OTA images are published by
`inkbot-esp32-publish.yml` on `main` (see [`inkbot-esp32/docs/ota.md`](inkbot-esp32/docs/ota.md)).

**The iOS app is tested by a separate workflow (`ios.yml`), not `test.yml`,**
because it needs a macOS runner. A cheap Linux `discover` job reuses the same
`discover-changed-apps.sh` logic (it emits an `ios` list) and only then
spins up a `macos-latest` job — so browser/Go/Rust-only PRs never pay for macOS
minutes. When `ios/` changed, CI runs XcodeGen → `bundle exec fastlane test`
(unit + UI tests on a Simulator; no signing needed). On push to `main` with
Apple signing secrets present, it additionally runs `fastlane beta` to upload to
TestFlight. PRs that need refreshed signing assets get a `needs-ios-bootstrap`
label; on merge, a separate workflow re-runs `signing_bootstrap` in parallel
(usually finishing before the build). Run discovery locally with:

```bash
bash .github/scripts/discover-ios-apps.sh --all
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-ios-apps.sh --from-changes
```

**macOS apps use the same pattern via `macos.yml`:** Linux discovery emits a
`macos` list (dirs whose `project.yml` has `platform: macOS`), then a
`macos-latest` job runs XcodeGen → `fastlane test`. On `main` with Developer ID
/ Sparkle secrets, it will run `fastlane beta` (notarize + appcast); without
secrets, tests still run and ship is skipped. Discovery:

```bash
bash .github/scripts/discover-macos-apps.sh --all
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-macos-apps.sh --from-changes
bash .github/scripts/discover-xcodegen-apps_test.sh   # ios vs macos marker tests
```

Run the per-type discovery helpers locally to see what CI would select:

```bash
# Every app of one type
bash .github/scripts/discover-testable-apps.sh --all   # browser
bash .github/scripts/discover-go-modules.sh --all      # Go
bash .github/scripts/discover-rust-apps.sh --all       # Rust
bash .github/scripts/discover-pasta.sh --all           # pasta style leg
bash .github/scripts/discover-blog.sh --all            # posts catalog
bash .github/scripts/discover-index.sh --all           # Pages home-page index

# Only what a diff touched (what CI uses on a PR)
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-rust-apps.sh --from-changes
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-pasta.sh --from-changes
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-blog.sh --from-changes
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-index.sh --from-changes
```

## Dependency updates (`deps.yaml`)

A scheduled workflow (daily at 00:00 UTC, or on demand via *Run workflow*) keeps
every app's dependencies fresh. For each app it upgrades dependencies with that
ecosystem's idiomatic tool, then verifies the result with the same checks the
test workflow gates on:

| App type | Upgrade | Verify |
|----------|---------|--------|
| Browser | `npx npm-check-updates --upgrade` → `npm install` → `npm run vendor` (if defined) | `npm test` (+ `npm run test:e2e` if defined) |
| Go | `go get -u ./...` | `go build ./...` → `go test -race ./...` |
| Rust | `cargo update` | `cargo clippy -D warnings` → `cargo test`; Worker apps also wasm clippy + a release `wasm32-unknown-unknown` build + the wrangler `[build]` command |

Publishing is all-or-nothing, so a green run never lands a half-broken bump:

- **Everything upgraded, built, and tested** → it opens (or updates) a pull
  request on `automation/dependency-updates` with the changed lockfiles/manifests
  (`go.mod`/`go.sum`, `package.json`/`package-lock.json` plus vendored output,
  `Cargo.toml`/`Cargo.lock`), enables auto-merge, and lets required status
  checks merge it into `main`. Direct pushes to `main` are blocked by branch
  protection, so the workflow federates an [Octo STS](https://github.com/octo-sts/app)
  GitHub App token (trust policy
  `.github/chainguard/dependency-updates.sts.yaml`) instead of using
  `GITHUB_TOKEN` — App-authored PRs trigger Actions checks; `GITHUB_TOKEN` ones
  do not. When there is nothing to bump, it closes any stale automation PR.
- **Any upgrade, build, or test fails** → it opens (or updates) the same pull
  request with whatever it could change — or an empty commit when nothing did —
  without auto-merge, so a human can finish the upgrade, and the run is marked
  failed.

Each ecosystem's work lives in its own script (`update-go-dependencies.sh`,
`update-js-dependencies.sh`, `update-rust-dependencies.sh`), and
`manage-dependency-update.sh` handles auto-merge / failure reporting. New apps
are discovered automatically — no workflow edits are needed.

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

## Adding a project post

A `blog-post.md` file anywhere in the source tree (except hidden and generated
directories) is published to `/posts/<parent-dir>/`. Dates come from git
author history. Local images referenced from the file are copied next to the
generated HTML; a missing image fails the build. The catalog also writes
`/posts/feed.xml` (RSS 2.0, newest first, full post HTML).

**Agents must not create, edit, or rewrite `blog-post.md` files.** Only a
human author writes those.

To preview the catalog locally:

```bash
python3 .github/scripts/build-blog.py --out /tmp/posts \
  --base-url https://example.github.io/playground/posts
python3 .github/scripts/build-blog_test.py
```

## Adding a new Go app

1. Create a **top-level directory** (for example, `my-tool/`).
2. Initialize an independent module at `my-tool/go.mod`.
3. Keep all Go sources and tests inside that directory.
4. Commit `go.sum` when the module has dependencies.
5. Add `my-tool/README.md` with build, run, and test instructions.
6. Add `my-tool/.gitignore` for local binaries and other generated output.
7. Do **not** add `index.html`; Go apps are not deployed or previewed on
   GitHub Pages. To ship a Go service on exe.dev instead, see
   [Adding an exe app](#adding-an-exe-app).

No workflow edits are required. CI discovers a new Go app from its `go.mod`,
and the daily dependency workflow includes it automatically.

Run locally:

```bash
cd my-tool
go build ./...
go test ./...
# CI runs `go test -race ./...` (pasta / node-image also get -timeout 30m)
```

## Adding an exe app

An **exe app** is a top-level directory whose `iac/` Terraform stack declares
the community [`benjamin-lykins/exedev`](https://registry.terraform.io/providers/benjamin-lykins/exedev)
provider. `deploy-exe.yml` discovers those apps the same way
`deploy-workers.yml` discovers `wrangler.toml`.

1. Put app sources in a top-level directory (for example `my-exe-app/`).
2. Add `my-exe-app/iac/` with:
   - `providers.tf` requiring `benjamin-lykins/exedev` and `ko-build/ko`
   - an S3 backend aimed at R2 bucket `playground-terraform-state` with key
     `exe/<app>/terraform.tfstate`
   - `ko_build.app` pushing to `ghcr.io/<owner>/playground/<app>` (set
     `repo` so the importpath is not appended)
   - `exedev_vm.app` using `ko_build.app.image_ref` as `image`
3. Keep the GHCR package **public** (the registry provider has no
   `registry_auth`; CI sets visibility after the first push).
4. Document required repo secrets in the app README
   (`EXEDEV_SSH_PRIVATE_KEY`; Cloudflare secrets are shared — CI mints
   short-lived R2 S3 credentials from `CLOUDFLARE_API_TOKEN`).

No workflow edits are required for a new exe app that follows this layout.
Discovery:

```bash
bash .github/scripts/discover-exe-apps.sh --all
git diff --name-only origin/main...HEAD | bash .github/scripts/discover-exe-apps.sh --from-changes
```

## Adding a new Rust app

1. Create a **top-level directory** (for example, `my-worker/`).
2. Initialize an independent crate at `my-worker/Cargo.toml` (include
   `[lints.rust] unused = "deny"`) and commit `Cargo.lock`.
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
 and rewritten to real ids before deploy, R2 buckets named by `[[r2_buckets]]`
  entries are created if absent, D1 databases declared in `[[d1_databases]]`
  have remote migrations applied, and a Worker that ships
 `examples/genvapid.rs` gets a `VAPID_PRIVATE_KEY` secret generated once (only
 if absent, so the key is stable across deploys). Every Worker must enable
 Workers Logs (including invocation logs) and Workers Traces in its
 `wrangler.toml` — the `wrangler_observability` pasta rule enforces this.
 Head sampling is 100% at playground traffic; dial down before serious
 volume.

No workflow edits are required. CI discovers a new Rust app from its
`Cargo.toml`, the deploy workflow discovers a new Worker from its
`wrangler.toml`, and the daily dependency workflow includes it automatically.

Run locally:

```bash
cd my-worker
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test
```

## Adding an experiment to the iOS app

There is only one iOS **host** app (`ios/`). Add functionality as an
**experiment** inside it — never as a new top-level iOS directory.

**Contract (host Bundle ID vs keyboard extension, when bootstrap is required):**
[`ios/AGENTS.md`](ios/AGENTS.md).

1. Create `ios/Sources/Experiments/<YourExperiment>/` — **one directory per
   experiment** — with a SwiftUI view. Keep the interesting logic in plain types
   so it can be unit-tested without a simulator; add accessibility identifiers
   to controls so UI tests can drive them.
2. In that folder, add a `*Experiment.swift` that exposes a static
   `experiment: Experiment` (stable unique `id`, title, summary, icon,
   destination). Ids double as UI-test accessibility identifiers.
3. Append that static to `ExperimentCatalog.all` in `ios/Sources/Experiment.swift`.
4. Add tests under `ios/Tests/PlaygroundTests/` (and a UI flow under
   `ios/Tests/PlaygroundUITests/` if useful).

In-app experiments need **no** new Bundle ID and **no** signing bootstrap. A
Custom Keyboard (or other app extension) is different — Apple requires a second
Bundle ID; see `ios/AGENTS.md`. TestFlight delivery needs Apple signing secrets
(`docs/ios-testflight-setup.md`); until then CI tests and skips upload.

Run locally (macOS + Xcode):

```bash
cd ios
brew install xcodegen && bundle install
xcodegen generate
bundle exec fastlane test
```

## Adding a new macOS app

1. Create a **top-level directory** (for example, `my-mac-app/`).
2. Add **`my-mac-app/project.yml`** (XcodeGen) with a target that declares
   **`platform: macOS`** — that line is what distinguishes it from the iOS app
   type (`platform: iOS`).
3. Keep sources, tests, `fastlane/`, and `Gemfile` inside that directory.
4. Add `my-mac-app/README.md` and a `.gitignore` (at least `*.xcodeproj`,
   `DerivedData/`, `*.dmg`).
5. Do **not** add `index.html`; macOS apps are not Pages browser apps.
6. Do **not** put the app under `ios/` — macOS apps are separate top-level apps.

No workflow edits are required for the test path. `macos.yml` discovers the app
from `platform: macOS`. Sparkle release on `main` needs Developer ID / notarization
secrets (see [`docs/macos-sparkle-design.md`](docs/macos-sparkle-design.md)).

Run locally (macOS + Xcode):

```bash
cd my-mac-app
brew install xcodegen && bundle install
xcodegen generate
bundle exec fastlane test
```

## Implementation conventions

- **Browser apps are client-side**: they must be static sites suitable for GitHub Pages (no server-side runtime in production).
- **Prefer plain HTML + JS** for browser apps unless an app already uses a framework; match the style of neighboring code in that app directory.
- **Go apps are independent modules**: each app owns its `go.mod` and `go.sum`; avoid cross-app imports.
- **Rust apps are independent crates**: each app owns its `Cargo.toml`, `Cargo.lock`, and `rust-toolchain.toml`; avoid cross-app imports. Each crate sets `[lints.rust] unused = "deny"` so unused methods, imports, and variables fail `cargo test` / `cargo build` (CI clippy also uses `-D warnings`, which includes rustc `dead_code` and clippy unused-* lints). Do not `#[allow(dead_code)]` to keep dead methods.
- **There is one iOS host app** (`ios/`, the "Playground" container): add
  features as **experiments** inside it (same Bundle ID, no re-bootstrap). A
  Custom Keyboard or other **app extension** needs a second Bundle ID (Apple
  rule) and a one-time match bootstrap — see [`ios/AGENTS.md`](ios/AGENTS.md).
  Never commit the generated `*.xcodeproj` or signing material.
- **macOS apps are independent top-level apps**: each owns its `project.yml`
  (`platform: macOS`), Bundle ID, and `fastlane/`. Do not nest them under `ios/`.
- **Keep all apps isolated**: do not add repo-root `package.json`, `go.mod`, `go.work`, or Cargo workspace files unless the maintainers explicitly request a monorepo toolchain.
- **Minimize scope**: when fixing or extending one app, avoid unrelated changes in other directories.
- **Comments and documentation**: follow the [Google developer documentation style guide](https://developers.google.com/style). Agents: read [`.cursor/skills/google-developer-style/SKILL.md`](.cursor/skills/google-developer-style/SKILL.md) before writing or editing comments, READMEs, or other docs.
- **Unslop**: when you write comments, docs, HTML copy, or PR prose, read [`.cursor/skills/unslop/SKILL.md`](.cursor/skills/unslop/SKILL.md) ([unslop](https://github.com/cursor/plugins/blob/HEAD/pstack/skills/unslop/SKILL.md) from cursor/plugins) and strip AI tells. Google style still owns headings, code font, inclusive language, and procedures. First person is fine in README ledes and PR descriptions.
- **Taglines**: do not invent taglines or slogans. If existing tagline copy should go, delete it and wait for an explicit replacement.
- **Visual design and typography**: when you design or restyle HTML, CSS, or Pages templates, read [`.cursor/skills/web-typography/SKILL.md`](.cursor/skills/web-typography/SKILL.md) (Wondel's [web-typography](https://skills.wondel.ai/skills/web-typography/) skill).
- **Do not commit**: `node_modules/`, secrets, env files, browser/Go/Rust build artifacts (`target/`), `*.xcodeproj`, `*.dmg`, or Playwright/Jest output (`test-results/`, `coverage/`).
- **Do not write `blog-post.md` files.** Those are human-authored project
  posts. Agents must not create, edit, or rewrite them. The published
  `/posts/` catalog is generated at deploy time from those files; do not
  commit generated HTML under `posts/`. The published `posts/` directory
  name is reserved (it is not a browser app).

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
- **Before pushing more commits to an existing PR branch, check that the PR
  is still open.** Humans often merge while an agent is mid-follow-up; pushing
  onto a merged branch confuses agents and leaves commits orphaned off `main`.
  If the PR is already merged (or closed), stop — branch fresh from `main` and
  open a new PR for the remaining work. Check with
  `gh pr view <number> --json state` (or the GitHub UI / PR URL) before
  `git push`.
- CI must pass (changed browser apps are tested; changed Go and Rust apps are built and tested).
- Preview deploy provides a live URL when a browser app, the posts catalog, or
  the Pages home-page index changed. Use it to verify browser behavior, especially mobile.
- If the repo uses Linear integration, include `Resolves ABC-123` in the PR body when applicable.

## Current browser apps

| Directory | Type | Tests |
|-----------|------|-------|
| `artillery/` | Turn-based artillery duel with local and AI modes | Node test runner |
| `cold-climb/` | Two-handle ball-climbing arcade game | Node test runner |
| `droneski/` | FPV drone filming a procedurally generated downhill skier | Node test runner |
| `esp-flash/` | Flash inkbot/maze (or a local `.bin`) to an ESP32 over Web Serial / WebUSB | Node test runner |
| `kubescheduler-the-game/` | Play the Kubernetes scheduler and cluster operator | Node test runner |
| `cors-proxy-demo/` | Browser playground for the `cors-proxy` Worker (send a request, inspect the CORS response) | none (static) |
| `git/` | In-browser read-only git client (clone, browse, branches, history) | Jest + Playwright |
| `hello/` | Static demo | none |
| `kanoodle/` | Kanoodle puzzle game (5×11 board, 12 pieces) | Jest + Playwright |
| `life-lab/` | Draw Life gen 0, preview the printable Z-stack in 3D, export STL / Bambu 3MF (wasm from `life-stl/`; rebuild via `life-lab/build-wasm.sh`) | Node test runner |
| `nypd-choppers/` | NYPD helicopter daily flight paths, hours, and fuel-cost estimates from ADS-B | Node test runner |
| `population-rays/` | Directional 5° population slices (distance to N people) over Meta/CIESIN HRSL grids | Node test runner |
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
| `chessh/` | Multiplayer chess over SSH (Bubble Tea + wish); deployed to exe.dev as `chessh.exe.xyz` via `deploy-exe.yml` | `go test -race ./...` |
| `gitdb/` | git repository explorer backed by SQLite virtual tables | `go test -race ./...` |
| `ocidb/` | OCI registry explorer backed by SQLite virtual tables | `go test -race ./...` |
| `pasta/` | CUE-described multi-language linters/fixers over tree-sitter ASTs; see [`pasta/AGENTS.md`](pasta/AGENTS.md). Playground style rules are enrolled via `.pasta/examples` → `pasta/analyzers` and gated by the pasta leg of `test.yml` | `go test -race ./...` (incl. e2e shallow-clone smoke); CI also runs `pasta test` + monorepo lint |

## Current Rust apps

| Directory | Type | Tests |
|-----------|------|-------|
| `web-push/` | Web Push backend — Cloudflare Worker (RFC 8030/8188/8291/8292) | `cargo test` + clippy + wasm build |
| `cors-proxy/` | SSRF-hardened CORS proxy — Cloudflare Worker | `cargo test` + clippy + wasm build |
| `inkbot/` | E-ink frame host + Slack `@inkbot` — Cloudflare Worker | `cargo test` + clippy + wasm build |
| `git-server/` | git smart-HTTP server on R2 + Durable Objects — Cloudflare Worker | `cargo test` (incl. real-git integration) + clippy + wasm build |
| `git-fuse/` | read-only FUSE adapter for git-server (mount commits/refs as files) — CLI, not a Worker | `cargo test` (incl. e2e over real FUSE mounts; skips without `/dev/fuse`) + clippy |
| `life-stl/` | Conway's Game of Life → 3D-printable STL (Z = time); self-supporting causality braces (default) or breakaway supports | `cargo test` + clippy |
| `mapvelopes/` | envelope PDFs with the sender-to-recipient route as the background (requires a Google Maps key; sizes #10, #9, Monarch, #6¾, A7) | `cargo test` + clippy + wasm build |
| `y/` | One-user microblog (D1 + R2); 260-char posts, images, RSS, passkeys | `cargo test` + clippy + wasm build |

> **`git-server` has its own agent guide:** read
> [`git-server/AGENTS.md`](git-server/AGENTS.md) before working in that
> directory. In particular, `git-server` exposes an HTTP API
> (`git-server/docs/api.md`), and any change that adds, removes, or alters an
> API method — a git smart-HTTP route or a `/api/…` endpoint — **must update
> `git-server/docs/api.md` in the same change**, keeping it an accurate list
> of everything the router handles.

## Other tools

These are not browser / Go / Rust / Apple apps, so shared CI does not
auto-discover them. Run their local tests when you change them.

| Directory | Type | Tests |
|-----------|------|-------|
| `its-not-jaws/` | Cursor SDK harness for It's Not Jaws (movie shared-fact guessing); mock backend for tests; live PR game via `its-not-jaws.yml` + `CURSOR_API_KEY` secret | `cd its-not-jaws && npm test` (CI also runs a live game when the secret is set) |
| `inkbot-esp32/` | Rust/ESP-IDF firmware: poll `inkbot` Worker and signed GHCR OTA, or `APP=maze` for an offline maze on the same 7.5″ panel. Secrets in NVS (`make provision`). Agent guide: [`inkbot-esp32/AGENTS.md`](inkbot-esp32/AGENTS.md) | host lib tests + provision dry-run + Xtensa cross-build via `inkbot-esp32.yml`; publish + Cosign on `main` via `inkbot-esp32-publish.yml` |
| `life-scad/` | OpenSCAD Life sculpture (Z = time) plus optional Python reverse-history search | `python3 life-scad/reverse_life_test.py` (needs `pip install -r life-scad/requirements.txt`) |
| `life-qr/` | Parametric OpenSCAD Life sculpture with a QR-code roof for any text/height | `python3 life-qr/life_qr_test.py` (optional `pip install segno`) |

## The iOS app

| Directory | Type | Tests |
|-----------|------|-------|
| `ios/` | The single "Playground" SwiftUI app — a launcher hosting experiments (e.g. Ride Monitor, T9 Keyboard); TestFlight CD on `main` | XCTest unit tests + XCUITest UI tests (`fastlane test`) |

## Current macOS apps

| Directory | Type | Tests |
|-----------|------|-------|
| `hello-macos/` | Minimal SwiftUI "Hello Mac" sample; notarized Sparkle CD + in-app updater | XCTest via `fastlane test` |
| `onramp/` | Onramp — offline can’t-get-online playbooks + network toolbox (+ optional chat); Sparkle CD | XCTest via `fastlane test` |

> **`onramp` has its own agent guide:** read
> [`onramp/AGENTS.md`](onramp/AGENTS.md) before working in that
> directory. Autonomous diagnostic tools **must never take action** — only
> read and diagnose. Confirmed click-to-run `SuggestedAction` buttons may open
> Settings/URLs or run allowlisted read-only probes and feed output back into
> another playbook pass; do not add mutating commands without an explicit
> product decision. Prefer the install-online → offline Can’t get online golden
> path over once-online Activity Monitor clones.

See each app's `README.md` for app-specific rules and local development.
