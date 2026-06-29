# git — local, read-only git client

Clone a git repository straight into your browser's local storage and browse it
like a mini code host: a file tree, a fast fuzzy file finder, a file viewer,
branch switching, and commit history. Everything runs on-device with
[isomorphic-git](https://isomorphic-git.org) and
[lightning-fs](https://github.com/isomorphic-git/lightning-fs) (IndexedDB).

> **Read-only.** This app never writes back to a remote. A future version may
> add an editing/commit flow; for now it only reads.

## Features

- **Clone into the browser** — paste an `https://` URL or `owner/repo` shorthand.
  The repo is stored in IndexedDB and reopens instantly on your next visit.
  Private repos can use a session-only access token (never persisted or logged).
- **Code browser** — collapsible file tree and a viewer with line numbers,
  offline syntax highlighting, language detection, image preview, a Markdown
  raw/preview toggle, and binary/large-file guards. Symlinks, submodules, and
  Git LFS pointers show a clear notice instead of raw bytes. The tree is fully
  keyboard-navigable.
- **File actions** — from the viewer header, copy a file's path or contents,
  download its raw bytes, or open it on its origin host (GitHub/GitLab/Bitbucket)
  when the clone URL is known.
- **Quick file finder** — fuzzy search across every file name. Press
  <kbd>Ctrl</kbd> / <kbd>Cmd</kbd> + <kbd>P</kbd>, or use the sidebar filter.
- **Content search** — grep across file *contents*. Press
  <kbd>Ctrl</kbd> / <kbd>Cmd</kbd> + <kbd>Shift</kbd> + <kbd>F</kbd>; supports
  literal or regex queries and opens each match at its line.
- **Off-main-thread search** — both the fuzzy index and content grep run in Web
  Workers (with a synchronous fallback), so searching stays smooth on big repos.
- **Scales to large repos** — the tree, filter results, and finder are
  virtualized (only the rows near the viewport are rendered), so a repository
  with tens of thousands of files stays responsive.
- **Browse any ref** — switch between branches, tags, or a specific commit
  (detached HEAD); the tree, viewer, and history follow.
- **Diff, history & blame** — view a commit's changed files with per-file line
  diffs, compare two refs, see the commit history for the repo or a single file,
  and blame a file to attribute each line to the commit that last changed it.
- **Deep links** — the repo, ref, file, and selected line range are encoded in
  the URL hash, so any view is shareable, bookmarkable, and reload-safe.
- **Pull / Update** — a menu action fetches the latest commits from the remote
  and reports how many new commits it pulled.
- **Stored repositories** — manage and reopen previously cloned repos (with an
  IndexedDB usage meter); remove to free space, or override the CORS proxy per
  repo. Clone/remove are coordinated across browser tabs. The last repo you had
  open is reoffered when you return to the bare URL.
- **Demo mode** — "Try a demo (no network)" loads a sample repo so you can see
  everything immediately, offline.

## Run locally

```bash
cd git
npm install
npm start         # serves the app at http://localhost:3000
```

Open the app, paste a repository URL (e.g. `isomorphic-git/isomorphic-git`),
and click **Clone**. Or click **Try a demo** to explore without a network.

## CORS proxy

Browsers cannot clone most git hosts directly because those servers don't send
the necessary CORS headers, so requests are routed through a CORS proxy. The app
defaults to the public `https://cors.isomorphic-git.org` proxy (configurable
under **Advanced options**, and overridable per repository from the stored-repos
list). That default is a third party that can see the repo URLs, any token, and
the content it relays, so for anything beyond casual or public use, run your own
proxy ([@isomorphic-git/cors-proxy](https://github.com/isomorphic-git/cors-proxy))
and set it there. Self-hosted CORS-enabled servers can clear the field.

## How it's built

No bundler or build step is needed to deploy — the app is plain ES modules plus
a few vendored libraries.

- `src/pathUtils.js` — POSIX path helpers
- `src/fileTree.js` — build/flatten the file tree from a flat path list
- `src/fuzzy.js` — fuzzy subsequence matcher + reusable search index
- `src/searchClient.js` / `src/searchWorker.js` — off-thread fuzzy file search
- `src/contentSearch.js` — grep query compiler + line scanner (pure)
- `src/contentSearchClient.js` / `src/contentSearchWorker.js` — off-thread content grep
- `src/highlightCode.js` — dependency-free, offline syntax highlighter
- `src/hashState.js` — deep-link state encoded in the URL hash
- `src/diff.js` — line-level (LCS) diff for the diff view
- `src/blame.js` — per-line blame from a file's per-commit history (pure)
- `src/repoUrl.js` — parse/validate clone URLs
- `src/language.js` — extension → language, image/binary detection
- `src/markdown.js` — safe, offline Markdown → HTML rendering
- `src/lfs.js` — detect Git LFS pointer blobs
- `src/specialEntry.js` — classify symlink/submodule tree entries, parse `.gitmodules`
- `src/hostUrl.js` — build "open on host" URLs for GitHub/GitLab/Bitbucket
- `src/format.js` — byte sizes, short oids, relative times
- `src/quota.js` — IndexedDB storage estimate/low-space helpers
- `src/auth.js` — session-only access-token store wired to `onAuth`
- `src/cloneError.js` — turn raw clone failures into a typed kind + friendly message
- `src/store.js` — observable store + first-class load controller
- `src/repoSource.js` — the read-only `RepoSource` interface + in-memory source
- `src/demoRepo.js` — sample repository for demo mode
- `src/gitClient.js` — isomorphic-git + lightning-fs adapter (lazy-loaded)
- `src/app.js` — entry point that boots the controller
- `src/controller.js` — repository lifecycle, load-race token, and module wiring
- `src/ui/dom.js` — DOM helpers and toast/progress/error feedback
- `src/ui/viewer.js` — file viewer (text/image/binary, highlight, line linking)
- `src/ui/tree.js` — sidebar tree, flat filter results, keyboard navigation
- `src/ui/palette.js` — command palette (fuzzy file finder)
- `src/ui/contentSearch.js` — content-search (grep) overlay
- `src/ui/history.js` — commit history panel + ref compare
- `src/ui/recent.js` — preset and stored repositories
- `src/ui/highlight.js` — shared fuzzy-match row rendering
- `src/ui/virtualList.js` — windowing helpers for the large-list virtualization
- `vendor/` — pre-bundled browser builds of the runtime libraries

The whole UI talks to a `RepoSource` interface, so demo mode and the real clone
share the exact same code browser. That also keeps the app fully testable
without a network.

### Re-vendoring

The runtime libraries are committed under `vendor/` so the deployed site has no
CDN dependency. After bumping versions in `package.json`:

```bash
npm install
npm run vendor    # refreshes vendor/ from node_modules (uses esbuild for the polyfill)
```

## Tests

```bash
npm test          # unit tests (Jest) — pure logic, RepoSource contract, real clone
npm run test:e2e  # browser tests (Playwright) — drive the demo repo, no network
npm run test:all  # both
```

The e2e tests run entirely against the built-in demo repository, so they never
touch the network while still exercising the real browser UI.

The Jest suite also includes an integration test
(`tests/realClone.integration.test.js`) that stands up a local
`git http-backend` server on `127.0.0.1` and drives the actual isomorphic-git
clone/fetch through `GitStorage` (with Node's `fs` + `git`/`http` injected).
It needs the `git` binary on `PATH` — present on standard CI — and skips
gracefully when `git http-backend` is unavailable. No external host is
contacted.
