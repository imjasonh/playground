# git — future work

A running, prioritized list of follow-ups for the `git` app. The base was
hardened first (correct Pull/Update ref resolution, scope-aware `update()`,
versioned repo registry, a load-race guard, ARIA tree semantics, and a
`GitRepoSource` unit suite). Since then the full **P1**, **P2**, and **P3**
rounds have all landed (see **Recently shipped**). What remains is the one large
project the read-only app deliberately deferred: an actual write/commit/push
flow.

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

**P3 round:**

- **Structured clone-error taxonomy** — `classifyCloneError` in `src/cloneError.js`
  reduces a raw failure to a stable `kind` (`quota`/`auth`/`network`/`not-found`/
  `unknown`) via ordered data rules, and `cloneErrorMessage` builds the friendly,
  actionable copy from that classification.
- **Git LFS pointer detection** — `src/lfs.js` recognizes an LFS pointer blob, so
  the viewer shows a "stored with Git LFS" notice (with the real size) instead of
  rendering the metadata stub as the file.
- **Viewer affordances** — copy path, copy contents, download the raw bytes, and
  "open on host" (GitHub/GitLab/Bitbucket, via `src/hostUrl.js`) from the viewer
  header, plus a loading skeleton in place of "Loading…" text.
- **Markdown preview** — safe, fully-offline Markdown rendering (`src/markdown.js`,
  with its own XSS-hardening tests) and a Raw/Preview toggle that sticks across
  files.
- **CORS proxy: privacy + per-repo override** — `GitStorage.setCorsProxy` plus an
  inline editor in the stored-repos list let each repo route through its own
  proxy, and an in-app note spells out the third-party hop the default implies.
- **Symlinks & submodules** — `src/specialEntry.js` classifies tree-entry modes
  and parses `.gitmodules`; the viewer shows a clear notice (symlink target, or a
  submodule's remote + pinned commit) instead of rendering a gitlink as bytes.
- **Blame** — per-line last-change attribution (`src/blame.js`): a pure algorithm
  over a file's history and its content at each commit, surfaced as a viewer
  "Blame" view where each contiguous run links back to the commit that wrote it.
  Works on real clones (`GitRepoSource.blame`) and in the demo
  (`InMemoryRepoSource.blame` over per-commit `fileVersions`).
- **UX polish** — reopen the last repo/ref/file when landing on the bare URL, an
  "N new commits" indicator after a fetch, and friendlier empty states (an empty
  repo vs. a no-match filter name it differently).

---

## Extensibility toward a write flow

The app is intentionally read-only today. The capability model and generalized
ref model prepared for an editing/commit flow; this is the flow itself, and the
only item left on this list.

### The actual write/commit/push flow (large)

Staging, commit authoring, and push — plus the hard parts: authentication
(tokens — the session-only PAT input already exists), conflict/merge handling,
and a clear "you are editing a local copy" mental model. The `capabilities`
model already carries `write`/`push` flags (every source reports them `false`
today) and the UI keys its affordances off them, so the seams exist; this is
still a project in itself, so capture requirements before starting.

Everything else from the earlier P1–P3 rounds has shipped (see **Recently
shipped** above).
