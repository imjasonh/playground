# git — local in-browser git client

Clone a git repository straight into your browser's local storage and browse it
like a mini code host: a file tree, a fast fuzzy file finder, a file viewer,
branch switching, and commit history — then **edit files, commit, and push**
back to the remote. Everything runs on-device with
[isomorphic-git](https://isomorphic-git.org) and
[lightning-fs](https://github.com/isomorphic-git/lightning-fs) (IndexedDB).

> **Read-write.** Edits, new files, deletions, and commits all happen in your
> browser's local clone. Nothing leaves your device until you explicitly push,
> which needs a personal access token (used only for that request, never stored).

## Features

- **Clone into the browser** — paste an `https://` URL or `owner/repo` shorthand.
  The repo is stored in IndexedDB and reopens instantly on your next visit.
- **Code browser** — collapsible file tree and a viewer with line numbers,
  language detection, image preview, and binary/large-file guards.
- **Edit, create, delete** — edit any text file in place, create new files, or
  delete existing ones. Changes are staged automatically.
- **Commit & push** — review staged changes in the Changes drawer, commit with
  an author + message, and push the branch back to its remote with a token.
- **Quick file finder** — fuzzy search across every file. Press
  <kbd>Ctrl</kbd> / <kbd>Cmd</kbd> + <kbd>P</kbd>, or use the sidebar filter.
- **Branch switching** — pick any branch; the tree, viewer, and history update.
- **Pull / Update** — a menu action fetches the latest commits from the remote.
- **Stored repositories** — manage and reopen previously cloned repos; remove to
  free space.
- **Demo mode** — "Try a demo (no network)" loads a sample repo so you can see
  everything — including the full edit → commit flow — immediately, offline.

## Editing, committing, and pushing

1. Open a text file and click **Edit**, use **+** in the sidebar to create a
   file, or **Delete** to remove one. Each change is staged into the local
   clone's index and marked in the tree.
2. Open the **Changes** drawer to review what's staged, set your author name and
   email (remembered locally), write a message, and **Commit**. The commit lands
   on the current branch in your in-browser clone.
3. To publish, enter a personal access token (and optionally a username) and
   **Push to remote**. The token is sent only with that request and is never
   written to disk. Pushing typically requires the same CORS proxy as cloning.

The demo repository is local-only, so it supports editing and committing but
hides the push controls.

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
- `src/repoSource.js` — the `RepoSource` interface (read + write) + in-memory source
- `src/demoRepo.js` — sample repository for demo mode
- `src/gitClient.js` — isomorphic-git + lightning-fs adapter (lazy-loaded)
- `src/app.js` — entry point that boots the controller
- `src/controller.js` — repository lifecycle, load-race token, and module wiring
- `src/ui/dom.js` — DOM helpers and toast/progress/error feedback
- `src/ui/viewer.js` — file viewer (text/image/binary, large-file guard)
- `src/ui/tree.js` — sidebar tree and flat filter results
- `src/ui/palette.js` — command palette (fuzzy file finder)
- `src/ui/history.js` — commit history panel
- `src/ui/editing.js` — edit/create/delete, the Changes drawer, commit + push
- `src/ui/recent.js` — preset and stored repositories
- `src/ui/highlight.js` — shared fuzzy-match row rendering
- `vendor/` — pre-bundled browser builds of the runtime libraries

The whole UI talks to a `RepoSource` interface, so demo mode and the real clone
share the exact same code browser and editing flow. That also keeps the app
fully testable without a network.

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
touch the network while still exercising the real browser UI — including the
edit → stage → commit flow.

The Jest suite also includes an integration test
(`tests/realClone.integration.test.js`) that stands up a local
`git http-backend` server on `127.0.0.1` and drives the actual isomorphic-git
clone/fetch through `GitStorage` (with Node's `fs` + `git`/`http` injected).
It needs the `git` binary on `PATH` — present on standard CI — and skips
gracefully when `git http-backend` is unavailable. No external host is
contacted.
