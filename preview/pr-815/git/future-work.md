# git — future work

A running, prioritized list of follow-ups for the `git` app. The base was
hardened first (correct Pull/Update ref resolution, scope-aware `update()`,
versioned repo registry, a load-race guard, ARIA tree semantics, and a
`GitRepoSource` unit suite). Since then the full **P1**, **P2**, and **P3**
rounds have all landed (see **Recently shipped**), plus background upstream
auto-update. What remains are two larger projects the read-only app deliberately
deferred: an actual write/commit/push flow, and a **size-aware clone strategy**
(full clone by default, shallow + narrow for very large repos, widening as you
browse).

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

**Since P3:**

- **Indexed content search** — the grep overlay (<kbd>Ctrl</kbd>/<kbd>Cmd</kbd> +
  <kbd>Shift</kbd> + <kbd>F</kbd>) no longer re-reads and re-scans every file on
  each keystroke. A **trigram index** (`src/contentIndex.js`) is built once for
  the default branch, keyed by its head commit oid, and persisted to IndexedDB
  (`src/contentIndexStore.js`, one record per repo so a new commit overwrites the
  stale one). A literal query intersects its trigrams' posting lists down to a
  small candidate set that is then scanned (still off the main thread, streaming,
  in `src/contentSearchWorker.js`) to confirm exact matches; regex / sub-trigram
  queries fall back to scanning every indexed text file. The built index is
  reused from memory across keystrokes and from IndexedDB across reopens/reloads.
  The index is **incrementally maintained**: the structure supports single-file
  add/remove/update, so a Pull/Update advances it by only the files that changed
  between the old and new commit (via `RepoSource.changedFiles`, wired through
  `syncContentIndex` in `src/controller.js` and `contentSearchClient.updateIndex`)
  instead of rebuilding. Clearing a repo from browser storage also deletes its
  index (`contentSearchClient.removeIndex`, wired into the stored-repos remove
  button). Covered by `tests/contentIndex.test.js`,
  `tests/contentIndexStore.test.js`, and `tests/contentSearchClient.test.js`
  (build-once/reuse, persistence, incremental update/remove, candidate
  narrowing), plus the existing content-search e2e.

  **Only the default branch is indexed for now.** Other refs (a different branch,
  a tag, or a detached commit) use an ephemeral, session-only index so a second
  persisted copy is never written. A natural next step is to index all branch
  heads and tags into a single **hybrid index that shares postings across refs**
  (most files are identical across branches) rather than storing N whole copies —
  e.g. key postings by blob oid and map each ref's tree to the blob oids it
  contains, so a trigram's posting list is stored once and reused by every ref
  that includes that blob.
- **Upstream auto-update** — while a cloned repo is open and the tab is visible,
  a visibility-aware poller (`src/poller.js`) peeks the remote with a lightweight
  `ls-remote` (`GitRepoSource.checkForUpdates`, via isomorphic-git's
  `listServerRefs`). When the current branch's remote tip has moved it
  auto-fetches the new commits into local storage, refreshes the view, and toasts
  how many arrived. The poll yields to any in-flight user action (a `busyDepth`
  guard plus the existing load-race token), pauses on a hidden tab, and never
  runs for the offline demo (no `fetch` capability). Covered by unit tests
  (`tests/poller.test.js`, `checkForUpdates` in `tests/gitClient.test.js`), a
  real-server peek in `tests/realClone.integration.test.js`, and e2e
  (`window.gitBrowser.pollNow()` drives a deterministic tick).

---

## Size-aware cloning: full by default, shallow + narrow for huge repos (large, design needed)

Today the clone scope is **manual**: the form defaults to `depth: 1`
(shallow) with "fetch all branches" on, and `GitStorage.clone` passes those
straight to isomorphic-git. The desired behavior is automatic:

> **Default to a full clone** (full history, all branches — the richest
> experience), **unless the repository is larger than ~100 MB**, in which case
> fall back to a **shallow + narrow** clone and **widen as the user browses**.

This is deferred because two of its three pieces need real design, and one of
them runs into an isomorphic-git limitation. Capture requirements before
building.

### 1. Detect the repository size *before* cloning

There is no size hint in the git smart-HTTP protocol itself, so size has to come
from the host's REST API:

| Host | Endpoint | Field |
|------|----------|-------|
| GitHub | `GET https://api.github.com/repos/{owner}/{repo}` | `size` (KiB) |
| GitLab | `GET /api/v4/projects/{id}?statistics=true` | `statistics.repository_size` (bytes) |
| Bitbucket | `GET /2.0/repositories/{ws}/{repo}` | `size` (bytes) |

Open questions: those APIs are CORS-enabled for GitHub/GitLab but rate-limited
(and need the session token for private repos); the URL parser in `repoUrl.js`
already extracts host + `owner/repo`, but **unknown/self-hosted hosts have no
size signal**. Fallback policy needs deciding — keep the current conservative
shallow default, or probe with a `depth: 1` clone and read the pack size before
committing to widening. `quota.js` already exposes IndexedDB headroom, which
should also feed the decision (a 100 MB repo may not fit at all).

### 2. Choose the clone scope from the size

- **≤ threshold** → full clone: `depth: 0`, all branches (today the form must be
  set by hand to get this).
- **> threshold (~100 MB, a named constant)** → shallow (`depth: 1`) **and**
  single-branch (the default ref only). The scope is already persisted in the
  registry and honored by `update()`/`fetch`, so this part is mostly wiring a
  pre-clone heuristic in front of `startClone`.

### 3. Widen as the user browses (the hard part)

"Narrow then widen" splits into three independent axes:

- **History depth** — feasible. Deepen a shallow clone on demand (e.g. when
  history/blame needs older commits) via `fetch({ depth: N })` /
  `fetch({ relative: true, depth: N })`. Add a `GitRepoSource.widenHistory(n)`
  that re-fetches deeper and clears the oid cache, plus a "fetch more history"
  affordance in the history/blame UI.
- **Branches** — feasible. On a single-branch clone, fetch a branch the first
  time the user selects it in the ref picker (the generalized ref model already
  lets the UI browse any ref; it just needs an on-demand fetch before the read).
- **Files/blobs (true "narrow" clone)** — **blocked today.** A real narrow clone
  is Git partial clone (`--filter=blob:none` / `blob:limit`) or sparse fetch,
  and **isomorphic-git implements neither** in the browser. Realistic options to
  evaluate: (a) accept that "narrow" means only shallow + single-branch and drop
  blob-level narrowing from scope; (b) lazy-load individual blobs from the host's
  raw/content API on open (abandons the "real on-device git" model and reintroduces
  per-file CORS/auth); or (c) implement partial-clone filters against the smart
  protocol (a substantial fork-level effort). This axis is the main reason the
  item is punted.

### Seams that already exist

- Clone params flow through `GitStorage.clone` and are stored per repo
  (`singleBranch`, `depth`, `corsProxy`); `update()` reuses them.
- `GitRepoSource.checkForUpdates`/`update` show the pattern for an on-demand,
  scope-preserving fetch that a `widenHistory`/`fetchRef` method would follow.
- A clear "this clone is shallow/narrow — fetch more" notice would reuse the
  existing toast + progress UI.

## Extensibility toward a write flow

The app is intentionally read-only today. The capability model and generalized
ref model prepared for an editing/commit flow; this is the flow itself, and the
other larger item left on this list (alongside size-aware cloning above).

### The actual write/commit/push flow (large)

Staging, commit authoring, and push — plus the hard parts: authentication
(tokens — the session-only PAT input already exists), conflict/merge handling,
and a clear "you are editing a local copy" mental model. The `capabilities`
model already carries `write`/`push` flags (every source reports them `false`
today) and the UI keys its affordances off them, so the seams exist; this is
still a project in itself, so capture requirements before starting.

Everything from the earlier P1–P3 rounds (plus upstream auto-update) has
shipped (see **Recently shipped** above); the write flow and size-aware cloning
are the two larger items that remain.
