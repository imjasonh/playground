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
- **Code browser** — collapsible file tree and a viewer with line numbers,
  language detection, image preview, and binary/large-file guards.
- **Quick file finder** — fuzzy search across every file. Press
  <kbd>Ctrl</kbd> / <kbd>Cmd</kbd> + <kbd>P</kbd>, or use the sidebar filter.
- **Branch switching** — pick any branch; the tree, viewer, and history update.
- **Pull / Update** — a menu action fetches the latest commits from the remote.
- **Stored repositories** — manage and reopen previously cloned repos; remove to
  free space.
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
under **Advanced options**). For anything beyond casual use, run your own proxy
([@isomorphic-git/cors-proxy](https://github.com/isomorphic-git/cors-proxy)) and
set it there. Self-hosted CORS-enabled servers can clear the field.

## How it's built

No bundler or build step is needed to deploy — the app is plain ES modules plus
a few vendored libraries.

- `src/pathUtils.js` — POSIX path helpers
- `src/fileTree.js` — build/flatten the file tree from a flat path list
- `src/fuzzy.js` — fuzzy subsequence matcher for the finder
- `src/repoUrl.js` — parse/validate clone URLs
- `src/language.js` — extension → language, image/binary detection
- `src/format.js` — byte sizes, short oids, relative times
- `src/repoSource.js` — the read-only `RepoSource` interface + in-memory source
- `src/demoRepo.js` — sample repository for demo mode
- `src/gitClient.js` — isomorphic-git + lightning-fs adapter (lazy-loaded)
- `src/app.js` — UI controller
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
