# git — future work

A running, prioritized list of follow-ups for the `git` app. The base was
recently hardened (correct Pull/Update ref resolution, scope-aware `update()`,
versioned repo registry, a load-race guard, ARIA tree semantics, and a
`GitRepoSource` unit suite), so the items here are deliberately the *next*
layer rather than known defects.

Priorities are a rough guide, not a schedule:

- **P1** — do before building much more on top; pays for itself in safety or velocity.
- **P2** — clearly valuable, not blocking.
- **P3** — nice to have / opportunistic.

---

## Architecture & maintainability

### Split `app.js` into modules (P1)

`src/app.js` is ~850 lines built around a single module-global `state` object
and a `dom` cache, with the controller, file viewer, sidebar/tree, command
palette, history panel, recent-repos list, and toast/progress helpers all
interleaved. It works, but it's the main thing that will slow down future
features and make them harder to test in isolation.

Proposed seams (behavior-preserving; keep every DOM id/class so the existing
e2e suite stays the safety net):

- `src/ui/dom.js` — `$`, `el`, `camel`, `debounce`, toast, progress, error helpers.
- `src/ui/viewer.js` — text/image/binary rendering, large-file guard, object-URL lifecycle (owns its own state + a `dispose()`).
- `src/ui/tree.js` — tree render + flat search results.
- `src/ui/palette.js` — the command palette + keyboard nav.
- `src/ui/history.js` — the commit history panel.
- `src/ui/recent.js` — stored/recent repos + presets.
- `src/controller.js` (or `store.js`) — the `RepoSource` lifecycle, the load
  token, and the cross-cutting state; everything else receives a small context
  instead of reaching into a global.

Do this as its **own PR** so the diff is a clean, reviewable move rather than
mixed in with behavior changes.

### Reduce shared mutable state (P2)

Once split, the global `state` is the remaining coupling point. Consider a tiny
observable/store so renders are explicit subscriptions and the load-token
pattern (see `loadToken` in `app.js`) becomes a first-class "current load"
concept instead of a hand-checked integer.

---

## Extensibility toward a write flow

The app is intentionally read-only today. The original ask left room for an
editing/commit flow later; these prepare for it without committing to it.

### Capability model on `RepoSource` (P2)

`readOnly` is currently a single boolean. Replace/augment it with a
`capabilities` shape (e.g. `{ read, fetch, write, push }`) so the UI can enable
affordances by capability rather than by knowing which concrete source it has.
See the `RepoSource` typedef in `src/repoSource.js`.

### Generalized ref model (P2)

The API is branch-centric (`getCurrentBranch` / `setBranch`). Generalize to a
ref concept that also covers **tags** and **arbitrary commits / detached
HEAD**, so you can browse at any point in history. `_resolveOid` in
`src/gitClient.js` already resolves arbitrary refs; the UI just doesn't expose
anything but branches.

### The actual write/commit/push flow (P3, large)

Staging, commit authoring, and push — plus the hard parts: authentication
(tokens), conflict/merge handling, and a clear "you are editing a local copy"
mental model. This is a project in itself; capture requirements before starting.

---

## Features

- **Tags & browse-at-commit (P2)** — surface tags in the picker and allow
  opening the tree at any commit (pairs with the ref model above).
- **Diff view (P2)** — clicking a commit in history shows its changed files and
  per-file diffs; also branch-vs-branch compare. isomorphic-git's `walk` over
  two `TREE`s gives the change set.
- **File history / blame (P2)** — `log` filtered by filepath for "history of
  this file"; blame is a stretch goal.
- **Content search (P2)** — grep-like search across file *contents*, not just
  names. Should run in a worker (see Performance) and stream results.
- **Syntax highlighting (P2)** — the viewer is plain text + line numbers today.
  Add a lightweight, vendorable highlighter (e.g. Shiki/highlight.js) — mind the
  bundle-size and the "no CDN, vendored offline" constraint in `vendor/`.
- **Markdown preview (P3)** — render `README.md` and friends with a raw/preview
  toggle.
- **Viewer affordances (P3)** — copy path, copy contents, download raw (esp. for
  binaries, which currently only show a notice), and "open on GitHub/host" when
  the origin URL is known.
- **Deep-linkable state (P2)** — encode repo + branch + file (+ line range) in
  the URL hash so views are shareable, bookmarkable, and survive reload. Only
  `#demo` is handled today (see `init()` in `app.js`).
- **Submodules / symlinks / Git LFS (P3)** — currently unhandled; at minimum
  detect and show a clear "not supported / pointer file" notice instead of
  rendering garbage.

---

## Performance & scale (large repos)

- **Virtualize the tree and palette lists (P1 for big repos)** — the debounce
  added to the sidebar filter only reduces *compute* per keystroke; rendering
  tens of thousands of DOM rows is the real bottleneck. Render only visible rows.
- **Move indexing into a Web Worker (P2)** — `listFiles` + building the fuzzy
  index can jank the main thread on huge repos. Precompute a search index off
  the main thread.
- **Storage-quota awareness (P2)** — surface IndexedDB usage, warn before
  cloning very large repos, and handle `QuotaExceededError` during clone
  gracefully (today it throws into the generic clone error path). Offer eviction
  from the stored-repos list.

---

## Robustness & correctness

- **Multi-tab coordination (P2)** — lightning-fs (IndexedDB) and the registry
  (localStorage) aren't coordinated across tabs; two tabs cloning/removing the
  same repo can race. Add a `BroadcastChannel`/`storage`-event sync and a lock
  around clone/remove in `GitStorage`.
- **Orphaned-dir cleanup (P2)** — a clone that fails mid-write can leave a
  half-populated dir in the FS even though the registry only records success
  (see `clone()` in `gitClient.js`). Add a "repair" pass that removes FS dirs not
  present in the registry, and clean up on clone failure.
- **Auth for private repos (P2)** — even read-only private repos need a token;
  there's no flow today. Plan a PAT input (session-only storage, never logged)
  wired to isomorphic-git's `onAuth`.
- **CORS proxy: privacy + per-repo override (P3)** — repo contents currently
  route through the public `cors.isomorphic-git.org` by default. We already store
  `corsProxy` per registry entry; expose it per-repo in the UI and add a short
  in-app privacy note about the third-party hop.
- **Structured error taxonomy (P3)** — `cloneErrorMessage` in `app.js`
  sniffs error strings with regexes. A small typed error mapping would be sturdier.

---

## Testing & CI

- **Integration test for the real clone/fetch path (P1)** — the biggest gap:
  CI can't reach external git hosts, so the actual isomorphic-git clone/fetch is
  unverified by automation. Stand up a **local** git HTTP server (a tmp repo
  served via `git http-backend`, or static dumb-HTTP) inside the test and clone
  from `127.0.0.1`, exercising `GitStorage.clone`/`open`/`update` for real
  without external egress.
- **`GitStorage` registry unit tests (P2)** — cover `listRepos` / `_upsert` /
  `_touch` round-tripping through localStorage under a jsdom env (the
  engine-dependent paths can stay mocked; `normalizeRegistry` is already tested).
- **Automated a11y checks (P2)** — run `axe` against the demo in the Playwright
  suite to catch regressions in the roles/labels we just added.
- **Keyboard navigation for the tree (P2)** — we added `role="tree"`/`treeitem`
  with `aria-expanded`, but not arrow-key movement/expand/collapse. Implement the
  key handling and assert it in e2e.

---

## UX polish (P3)

- Remember the last-opened repo/branch and restore it on load.
- Loading skeletons instead of "Loading…" text.
- An ahead/behind indicator after a fetch ("3 new commits").
- Friendlier empty/error states throughout.
