# git — future work

A running, prioritized list of follow-ups for the `git` app. The base was
hardened first (correct Pull/Update ref resolution, scope-aware `update()`,
versioned repo registry, a load-race guard, ARIA tree semantics, and a
`GitRepoSource` unit suite). Since then the full **P1** and **P2** rounds have
landed (see **Recently shipped**); what remains below is the **P3** layer —
nice-to-have / opportunistic work, plus the one large write-flow project.

Priorities are a rough guide, not a schedule:

- **P1** — do before building much more on top; pays for itself in safety or velocity.
- **P2** — clearly valuable, not blocking.
- **P3** — nice to have / opportunistic.

---

## Recently shipped

**P1 round:**

- **`app.js` split into modules** (#8) — `src/app.js` is now a thin bootstrap;
  the controller and UI concerns live in `src/controller.js` and `src/ui/*`
  (`dom`, `viewer`, `tree`, `palette`, `history`, `recent`, `highlight`), each
  handed a small context object instead of reaching into a module global.
- **Real clone/fetch integration test** (#9) — `tests/realClone.integration.test.js`
  stands up a local `git http-backend` server on `127.0.0.1` and drives
  `GitStorage.clone`/`open`/`update` for real. `GitStorage` now accepts an
  injected `fs`/`git`/`http` engine so the same code runs under Node, with no
  external host required.
- **List virtualization for large repos** (#11) — the tree, flat filter
  results, and command palette render only the visible window via
  `src/ui/virtualList.js`, so tens of thousands of files no longer mean tens of
  thousands of DOM rows.

**P2 round:**

- **Observable store + first-class load controller** — `src/store.js` funnels
  every state write through `setState`/`update` so cross-cutting concerns (e.g.
  the URL-hash sync) subscribe instead of being wired in by hand, and the old
  hand-incremented load token became `createLoadController`.
- **Capability model on `RepoSource`** — `capabilitiesOf` returns
  `{ read, fetch, write, push }` and the UI enables affordances by capability
  (see `applyCapabilities` in `src/controller.js`) rather than by sniffing the
  concrete source type.
- **Generalized ref model** — refs now cover branches, tags, and arbitrary
  commits / detached HEAD (`refValue`/`parseRefValue`/`setRef` in
  `src/repoSource.js`), surfaced through the ref picker.
- **Tags & browse-at-commit** — the picker groups Branches/Tags and shows a
  "Viewing" entry for a detached commit, so you can browse the tree at any point
  in history.
- **Diff view** — clicking a commit shows its changed files and per-file line
  diffs (`src/diff.js`), plus ref-to-ref compare, via a `walk` over two `TREE`s.
- **File history** — `log` filtered by filepath ("history of this file") from the
  viewer header. (Blame is still open below.)
- **Content search** — grep across file *contents*, not just names
  (`src/contentSearch.js`), running in a Web Worker
  (`src/contentSearchWorker.js`) and streaming results grouped by file; each
  match opens the file at its line.
- **Syntax highlighting** — a small, dependency-free, fully-offline tokenizer
  (`src/highlightCode.js`) colors the viewer for the common languages, with token
  colors tuned to WCAG AA.
- **Deep-linkable state** — repo + ref + file + line range live in the URL hash
  (`src/hashState.js`), so views are shareable, bookmarkable, and survive reload;
  the viewer supports click-to-link line targeting.
- **Indexing in a Web Worker** — building and scanning the fuzzy file index runs
  off the main thread (`src/searchWorker.js` / `src/searchClient.js`), with a
  synchronous fallback when Workers are unavailable.
- **Storage-quota awareness** — `src/quota.js` surfaces IndexedDB usage, warns
  before cloning when low, and turns `QuotaExceededError` into a clear message.
- **Multi-tab coordination** — a per-dir lock (Web Locks API, with a fallback)
  serializes clone/remove across tabs, and a `storage`-event sync keeps the
  stored-repos list fresh.
- **Orphaned-dir cleanup** — clone failures clean up their partial dir, and a
  background `repair()` pass removes FS dirs the registry doesn't know about.
- **Auth for private repos** — a session-only PAT input (never persisted/logged)
  wired to isomorphic-git's `onAuth` (`src/auth.js`).
- **`GitStorage` registry unit tests** — a jsdom suite covers `_upsert`/`_touch`
  (`tests/gitStorage.test.js`).
- **Automated a11y checks** — `@axe-core/playwright` scans the demo, palette,
  history panel, and content-search overlay against WCAG 2.0/2.1 A & AA.
- **Keyboard navigation for the tree** — arrow-key movement, expand/collapse, and
  Home/End following the WAI-ARIA tree pattern, asserted in e2e.

---

## Extensibility toward a write flow

The app is intentionally read-only today. The capability model and generalized
ref model above prepared for an editing/commit flow; this is the flow itself.

### The actual write/commit/push flow (P3, large)

Staging, commit authoring, and push — plus the hard parts: authentication
(tokens — the session-only PAT input already exists), conflict/merge handling,
and a clear "you are editing a local copy" mental model. This is a project in
itself; capture requirements before starting.

---

## Features

- **Blame (P3)** — annotate each line with its last-changing commit. A stretch
  goal left over from file history; pairs with the existing per-file `log`.
- **Markdown preview (P3)** — render `README.md` and friends with a raw/preview
  toggle.
- **Viewer affordances (P3)** — copy path, copy contents, download raw (esp. for
  binaries, which currently only show a notice), and "open on GitHub/host" when
  the origin URL is known.
- **Submodules / symlinks / Git LFS (P3)** — currently unhandled; at minimum
  detect and show a clear "not supported / pointer file" notice instead of
  rendering garbage.

---

## Robustness & correctness

- **CORS proxy: privacy + per-repo override (P3)** — repo contents currently
  route through the public `cors.isomorphic-git.org` by default. We already store
  `corsProxy` per registry entry; expose it per-repo in the UI and add a short
  in-app privacy note about the third-party hop.
- **Structured error taxonomy (P3)** — `cloneErrorMessage` in `src/cloneError.js`
  sniffs error strings with regexes. A small typed error mapping would be sturdier.

---

## UX polish (P3)

- Remember the last-opened repo/branch and restore it on load. (Deep links cover
  the explicit case; this is the implicit "reopen what I had" case.)
- Loading skeletons instead of "Loading…" text.
- An ahead/behind indicator after a fetch ("3 new commits").
- Friendlier empty/error states throughout.
