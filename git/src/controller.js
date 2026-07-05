/**
 * App controller: owns the cross-cutting state, the repository lifecycle
 * (clone / open / branch switch / update), and the load-race token, and wires
 * the UI modules together. Each UI module receives a small `ctx` instead of
 * reaching into a module global, so the seams here are the only place that
 * knows about all of them at once.
 */
import { cacheDom, createFeedback, debounce, el } from './ui/dom.js';
import { createViewer } from './ui/viewer.js';
import { createTree } from './ui/tree.js';
import { createPalette } from './ui/palette.js';
import { createContentSearch } from './ui/contentSearch.js';
import { createHistory } from './ui/history.js';
import { createRecent } from './ui/recent.js';
import { createShare } from './ui/share.js';
import { buildFileTree } from './fileTree.js';
import { createStore, createLoadController } from './store.js';
import { createUpdatePoller } from './poller.js';
import { capabilitiesOf, refLabel, refValue, parseRefValue } from './repoSource.js';
import { diffLines } from './diff.js';
import { isBinaryExtension, looksBinary } from './language.js';
import { ancestors } from './pathUtils.js';
import { parseRepoUrl, DEFAULT_CORS_PROXY } from './repoUrl.js';
import { fileWebUrl } from './hostUrl.js';
import { commitSummary, shortOid, countNewCommits, newCommitsPhrase } from './format.js';
import { cloneErrorMessage } from './cloneError.js';
import { rememberToken } from './auth.js';
import { storageEstimate, describeStorage, isLowOnStorage } from './quota.js';
import { createDemoSource } from './demoRepo.js';
import { parseHash, encodeHashState } from './hashState.js';
import { createSearchClient } from './searchClient.js';
import { createContentSearchClient } from './contentSearchClient.js';

// Every element id the UI looks up. Kept in one list so the static wiring test
// can confirm each one exists in index.html.
const DOM_IDS = [
  'repo-bar', 'repo-name', 'repo-meta', 'branch-select', 'find-btn', 'search-btn',
  'history-btn', 'update-btn', 'share-btn', 'close-btn', 'start-view', 'clone-form',
  'share-overlay', 'share-url', 'share-copy-btn', 'share-close-btn', 'share-qr', 'share-hint',
  'url-input', 'ref-input', 'depth-input', 'allbranches-input', 'proxy-input', 'token-input',
  'clone-btn', 'demo-btn', 'preset-list', 'clone-error', 'clone-progress', 'progress-fill',
  'progress-label', 'recent', 'recent-list', 'storage-usage', 'browser-view', 'tree-filter',
  'file-tree', 'flat-results', 'tree-empty', 'viewer-head', 'file-path',
  'file-info', 'file-copy-path-btn', 'file-copy-btn', 'file-download-btn', 'file-open-btn',
  'file-blame-btn', 'file-history-btn', 'viewer-body', 'viewer-placeholder', 'history-panel',
  'history-branch', 'history-compare', 'compare-select', 'commit-list', 'palette', 'palette-input',
  'palette-results', 'palette-empty', 'content-search', 'content-search-input', 'cs-case',
  'cs-regex', 'content-search-status', 'content-search-results', 'content-search-empty', 'toast',
];

// Where the "reopen what I had" session (last repo + ref + file) is remembered.
// Distinct from the deep-link hash: this covers landing on the bare URL.
const LAST_SESSION_KEY = 'git-browser:last';

export async function init() {
  const dom = cacheDom(DOM_IDS);
  const feedback = createFeedback(dom);
  const { toast, hideToast, showProgress, hideProgress, showError, hideError } = feedback;

  const store = createStore({
    storage: null,
    source: null,
    files: [],
    fileSet: new Set(),
    tree: null,
    expanded: new Set(),
    activePath: null,
    branches: [],
    tags: [],
    lines: null, // selected line range {start,end} in the active text file
    historyOpen: false,
    historyPath: null, // when set, the history panel shows this file's history
  });
  // `state` is the single live read view; every write flows through the store.
  const state = store.getState();

  // First-class "current load" shared by every async load (open / branch switch
  // / update). Each load supersedes the previous one and re-checks `active`
  // after every await, so a slower in-flight load can never overwrite the view
  // produced by a newer one.
  const loads = createLoadController();
  // A second, finer-grained load controller for the viewer pane alone, so
  // opening a file and showing a diff supersede each other cleanly.
  const viewLoads = createLoadController();
  const decoder = new TextDecoder('utf-8', { fatal: false });

  // Depth of in-flight, user-initiated loads (open / branch switch / manual
  // update). The background update poller yields whenever this is > 0 so an
  // automatic fetch never clobbers something the user is actively doing.
  let busyDepth = 0;
  // Polls the upstream while a fetch-capable repo is open and the tab is
  // visible; on each live tick it peeks for new commits and auto-fetches them
  // (see pollForUpdates). Created here, started/stopped as the source changes.
  const poller = createUpdatePoller({ onPoll: pollForUpdates });

  // Off-main-thread fuzzy file search (with a synchronous fallback). Shared by
  // the command palette and the tree filter; the controller keeps its corpus in
  // sync with the loaded file list (see reloadFiles / showStart).
  const search = createSearchClient();
  // Off-main-thread content (grep) search. Reads come from the RepoSource on the
  // main thread; the worker decodes + scans and streams matches back.
  const contentSearch = createContentSearchClient();

  // The shared context handed to each UI module. Cross-module actions are
  // assigned below, after the modules exist; modules only call them at
  // event time, so the late binding is safe.
  const ctx = { state, store, dom, toast, hideToast, search, contentSearch };

  const viewer = createViewer(ctx);
  const tree = createTree(ctx);
  const palette = createPalette(ctx);
  const contentSearchUI = createContentSearch(ctx);
  const history = createHistory(ctx);
  const recent = createRecent(ctx);
  const share = createShare(ctx);

  ctx.openFile = openFile;
  ctx.openSource = openSource;
  ctx.startClone = startClone;
  ctx.browseRef = switchRef;
  ctx.showCommitDiff = showCommitDiff;
  ctx.showCompare = showCompare;
  // Whether the active source can attribute lines to commits (blame). The
  // viewer keys the Blame affordance off this so it never offers blame for a
  // source that can't compute it. (The Blame button's click is wired in
  // bindEvents, alongside History.)
  ctx.canBlame = () => Boolean(state.source && typeof state.source.blame === 'function');
  // Web URL for the active file on its origin host (GitHub/GitLab/Bitbucket),
  // or null for the demo / an unknown host. The viewer uses this to decide
  // whether to offer the "Open" link and where it points.
  ctx.fileWebUrl = (path, lines) => {
    const source = state.source;
    if (!source || !source.url) return null;
    return fileWebUrl(source.url, { ref: currentRef().name, path, lines: lines || null });
  };
  // The viewer calls this when a line number is clicked, so the selection
  // becomes part of the shareable URL hash.
  ctx.onLinesChange = (range) => {
    store.setState({ lines: range });
    syncHash();
  };

  // Hash/deep-link bookkeeping: the value (without '#') we last wrote or read,
  // used to tell our own writes apart from real navigation; and a guard that
  // suppresses interim writes while a deep link is being applied.
  let lastHash = null;
  let restoring = false;

  dom.proxyInput.value = DEFAULT_CORS_PROXY;

  const { GitStorage } = await import('./gitClient.js').catch(() => ({}));
  if (GitStorage) {
    const storage = new GitStorage();
    store.setState({ storage });
    // Keep the stored-repos list in sync when another tab clones/removes a repo.
    if (typeof storage.onReposChanged === 'function') {
      storage.onReposChanged(() => recent.renderRecent());
    }
    // Reconcile the FS with the registry in the background: a clone that failed
    // before it was recorded can leave an orphaned dir behind. Best-effort.
    storage
      .repair()
      .then((removed) => {
        if (removed && removed.length) {
          toast(`Cleaned up ${removed.length} orphaned clone${removed.length > 1 ? 's' : ''}.`);
        }
      })
      .catch(() => {});
  }

  bindEvents();
  recent.renderPresets();
  recent.renderRecent();

  // Restore a deep-linked view (repo + ref + file + lines) from the URL hash,
  // and keep responding to later hash navigation (back/forward, shared links).
  lastHash = location.hash.replace(/^#/, '');
  window.addEventListener('hashchange', onHashChange);
  const initialState = parseHash(location.hash);
  if (initialState) {
    applyDeepLink(initialState);
  } else {
    // No explicit deep link: reopen the last repo/ref/file if we remember one.
    const last = loadLastSession();
    if (last) applyDeepLink(last);
  }

  window.gitBrowser = { openDemo, openSource, state, store, search, contentSearch, pollNow: pollForUpdates };

  /* ---------------------------------------------------------------- */
  /* Event wiring                                                      */
  /* ---------------------------------------------------------------- */

  function bindEvents() {
    dom.cloneForm.addEventListener('submit', onCloneSubmit);
    dom.demoBtn.addEventListener('click', openDemo);
    dom.closeBtn.addEventListener('click', onCloseRepo);
    dom.branchSelect.addEventListener('change', onRefChange);
    dom.updateBtn.addEventListener('click', onUpdate);
    dom.historyBtn.addEventListener('click', () => history.toggle());
    dom.fileBlameBtn.addEventListener('click', () => {
      if (state.activePath) showBlame(state.activePath);
    });
    dom.fileHistoryBtn.addEventListener('click', () => {
      if (state.activePath) history.showFile(state.activePath);
    });
    dom.findBtn.addEventListener('click', () => palette.open());
    dom.searchBtn.addEventListener('click', () => contentSearchUI.open());
    dom.shareBtn.addEventListener('click', () => share.open());
    // Debounced: the tree filter rescans every file on each keystroke, which is
    // wasted work on large repos when someone is typing quickly.
    dom.treeFilter.addEventListener('input', debounce(() => tree.renderSidebar(), 90));
    dom.paletteInput.addEventListener('input', () => palette.render());

    document.addEventListener('keydown', onGlobalKey);
    dom.palette.addEventListener('click', (e) => {
      if (e.target === dom.palette) palette.close();
    });
    dom.paletteInput.addEventListener('keydown', (e) => palette.onKey(e));
  }

  function onGlobalKey(event) {
    const mod = event.metaKey || event.ctrlKey;
    const key = event.key.toLowerCase();
    // Ctrl/Cmd+Shift+F: search file contents (grep). Checked before the plain
    // find shortcut so the two don't fight over modifier combos.
    if (mod && event.shiftKey && key === 'f' && state.source) {
      event.preventDefault();
      palette.close();
      if (contentSearchUI.isOpen()) contentSearchUI.close();
      else contentSearchUI.open();
      return;
    }
    if (mod && !event.shiftKey && key === 'p' && state.source) {
      event.preventDefault();
      contentSearchUI.close();
      if (palette.isOpen()) palette.close();
      else palette.open();
      return;
    }
    if (event.key === 'Escape') {
      if (palette.isOpen()) palette.close();
      if (contentSearchUI.isOpen()) contentSearchUI.close();
      if (share.isOpen()) share.close();
    }
  }

  /* ---------------------------------------------------------------- */
  /* View switching                                                    */
  /* ---------------------------------------------------------------- */

  /** The explicit "close repo" affordance: forget the session, then go home. */
  function onCloseRepo() {
    clearLastSession();
    showStart();
  }

  function showStart() {
    loads.cancel();
    poller.stop();
    store.setState({ source: null, activePath: null, lines: null });
    search.setFiles([]); // drop the corpus so the worker isn't holding a stale repo
    viewer.dispose();
    dom.browserView.hidden = true;
    dom.repoBar.hidden = true;
    dom.startView.hidden = false;
    document.body.classList.remove('repo-open');
    palette.close();
    contentSearchUI.close();
    share.close();
    recent.renderRecent();
    syncHash();
  }

  function showBrowser() {
    dom.startView.hidden = true;
    dom.browserView.hidden = false;
    dom.repoBar.hidden = false;
    document.body.classList.add('repo-open');
  }

  /* ---------------------------------------------------------------- */
  /* Clone / open                                                      */
  /* ---------------------------------------------------------------- */

  function onCloneSubmit(event) {
    event.preventDefault();
    startClone();
  }

  async function startClone() {
    hideError();

    const parsed = parseRepoUrl(dom.urlInput.value);
    if (!parsed.valid) {
      showError(parsed.error);
      return;
    }
    if (!state.storage) {
      showError('The git engine failed to load. Reload the page and try again.');
      return;
    }

    const depth = parseInt(dom.depthInput.value, 10);
    const singleBranch = !dom.allbranchesInput.checked;
    const ref = dom.refInput.value.trim();
    const corsProxy = dom.proxyInput.value.trim();

    // Stash any access token for this host in session storage so the clone (and
    // later fetches) can authenticate. Never persisted to disk or logged.
    const token = dom.tokenInput ? dom.tokenInput.value.trim() : '';
    if (token) rememberToken(parsed.host, token);

    // Non-blocking heads-up when IndexedDB is nearly full. A small repo may
    // still fit, so warn rather than block; a real overflow surfaces a clear
    // QuotaExceededError message from cloneErrorMessage.
    const estimate = await storageEstimate();
    if (isLowOnStorage(estimate)) {
      toast(`Low on storage — ${describeStorage(estimate)}. Remove a stored repo if the clone fails.`, 'error');
    }

    setCloning(true);
    showProgress('Connecting…', 0);

    try {
      const source = await state.storage.clone({
        url: parsed.url,
        dir: parsed.dir,
        fullName: parsed.fullName,
        ref: ref || undefined,
        depth: Number.isFinite(depth) ? depth : 0,
        singleBranch,
        corsProxy,
        onProgress: (p) => {
          const pct = p.total ? Math.round((p.loaded / p.total) * 100) : null;
          showProgress(p.phase || 'Working…', pct);
        },
        onMessage: (msg) => showProgress(String(msg).trim(), null),
      });
      await openSource(source);
      toast(`Cloned ${parsed.fullName}`, 'success');
    } catch (err) {
      showError(cloneErrorMessage(err, corsProxy));
    } finally {
      setCloning(false);
      hideProgress();
    }
  }

  function setCloning(busy) {
    dom.cloneBtn.disabled = busy;
    dom.cloneBtn.textContent = busy ? 'Cloning…' : 'Clone';
    dom.demoBtn.disabled = busy;
    for (const button of dom.presetList.querySelectorAll('button')) {
      button.disabled = busy;
    }
  }

  async function openSource(source) {
    busyDepth += 1;
    try {
      store.setState({ source, activePath: null, lines: null, expanded: new Set() });
      viewer.dispose();
      history.reset();
      applyCapabilities(source);
      // Match the background poller to the new source (runs only for a source
      // that can fetch; stopped for the demo and on close).
      syncPoller();

      const load = loads.begin();
      showBrowser();
      tree.resetScroll();
      await refreshRepo(load);
      if (!load.active) return;
      viewer.showPlaceholder();
      syncHash();
    } finally {
      busyDepth -= 1;
    }
  }

  /** Start or stop the upstream poller to match the current source. */
  function syncPoller() {
    if (state.source && capabilitiesOf(state.source).fetch) poller.start();
    else poller.stop();
  }

  /** Enable/disable repo-bar affordances based on what the source supports. */
  function applyCapabilities(source) {
    const caps = capabilitiesOf(source);
    dom.updateBtn.disabled = !caps.fetch;
    dom.updateBtn.title = caps.fetch
      ? 'Fetch the latest commits from the remote'
      : 'This source has no remote to fetch from';
  }

  /** Reload branch list, files, and header for the current branch. */
  async function refreshRepo(load) {
    const source = state.source;
    dom.repoName.textContent = source.fullName;

    const [branches, tags] = await Promise.all([
      source.listBranches(),
      typeof source.listTags === 'function' ? source.listTags().catch(() => []) : [],
    ]);
    if (!load.active) return;
    store.setState({ branches, tags });
    renderRefPicker();

    await reloadFiles(load);
    if (!load.active) return;

    try {
      const head = await source.headCommit();
      if (!load.active) return;
      renderHead(head);
    } catch {
      dom.repoMeta.textContent = '';
    }

    if (state.historyOpen) history.load();
  }

  async function reloadFiles(load) {
    const files = await state.source.listFiles();
    if (!load.active) return;
    const fileTree = buildFileTree(files);
    store.setState({
      files,
      fileSet: new Set(files),
      tree: fileTree,
      // Auto-expand a single top-level directory chain for convenience.
      expanded: initialExpanded(fileTree),
    });
    // Hand the new corpus to the search backend (rebuilds the index off-thread).
    search.setFiles(files);
    dom.treeFilter.value = '';
    tree.renderSidebar();
  }

  /** Set of directory paths forming the single top-level chain to auto-open. */
  function initialExpanded(fileTree) {
    const expanded = new Set();
    let nodes = fileTree.children;
    while (nodes.length === 1 && nodes[0].type === 'dir') {
      expanded.add(nodes[0].path);
      nodes = nodes[0].children;
    }
    return expanded;
  }

  function renderHead(head) {
    if (!head) {
      dom.repoMeta.textContent = `${state.files.length} files`;
      return;
    }
    dom.repoMeta.textContent =
      `${refLabel(currentRef())} · ${shortOid(head.oid)} · ` +
      `${commitSummary(head.message)} · ${state.files.length} files`;
  }

  /** The current ref descriptor, tolerating sources without getCurrentRef. */
  function currentRef() {
    const source = state.source;
    if (source && typeof source.getCurrentRef === 'function') return source.getCurrentRef();
    return { type: 'branch', name: source ? source.getCurrentBranch() : '' };
  }

  /** Render the branch/tag/commit picker reflecting the current ref. */
  function renderRefPicker() {
    const select = dom.branchSelect;
    select.replaceChildren();
    const current = currentRef();
    const currentValue = refValue(current);

    appendRefGroup(select, 'Branches', state.branches.map((b) => ['branch', b.name, b.name]));
    appendRefGroup(select, 'Tags', state.tags.map((t) => ['tag', t, t]));

    // Surface whatever ref is being viewed even when it isn't a listed branch
    // or tag (a detached commit, or a tag/branch the source didn't enumerate).
    const known = [...select.options].some((o) => o.value === currentValue);
    if (!known && current.name) {
      appendRefGroup(select, 'Viewing', [[current.type, current.name, refLabel(current)]]);
    }

    select.value = currentValue;
    const switchable = state.branches.length + state.tags.length;
    // Keep it interactive while detached so you can get back to a branch.
    select.disabled = switchable <= 1 && known;
  }

  function appendRefGroup(select, label, entries) {
    if (!entries.length) return;
    const group = el('optgroup');
    group.label = label;
    for (const [type, name, text] of entries) {
      const option = el('option', null, text);
      option.value = refValue({ type, name });
      group.appendChild(option);
    }
    select.appendChild(group);
  }

  function onRefChange() {
    switchRef(parseRefValue(dom.branchSelect.value));
  }

  /** Apply a ref via setRef when supported, else fall back to setBranch. */
  function applyRef(ref) {
    const source = state.source;
    if (typeof source.setRef === 'function') return source.setRef(ref);
    if (ref.type === 'branch') return source.setBranch(ref.name);
    return Promise.reject(new Error('This source cannot browse tags or commits.'));
  }

  /** Switch the view to any ref (branch / tag / commit) and refresh. */
  async function switchRef(ref, { quiet = false } = {}) {
    if (!state.source) return;
    busyDepth += 1;
    const load = loads.begin();
    try {
      await applyRef(ref);
      await refreshRepo(load);
      if (!load.active) return; // a newer switch/update superseded us

      // Re-open the active file on the new ref if it still exists.
      if (state.activePath && state.fileSet.has(state.activePath)) {
        openFile(state.activePath);
      } else {
        store.setState({ activePath: null, lines: null });
        viewer.showPlaceholder();
        syncHash();
      }
      if (!quiet) toast(`Switched to ${refLabel(ref)}`);
    } catch (err) {
      if (load.active) toast(`Could not switch: ${err.message}`, 'error');
    } finally {
      busyDepth -= 1;
    }
  }

  async function onUpdate() {
    if (!state.source) return;
    busyDepth += 1;
    const load = loads.begin();
    const btn = dom.updateBtn;
    btn.disabled = true;
    const original = btn.textContent;
    btn.textContent = 'Updating…';
    try {
      const result = await state.source.update((p) => {
        btn.textContent = p.phase ? `${p.phase}…` : 'Updating…';
      });
      await refreshRepo(load);
      if (load.active) {
        if (state.activePath && state.fileSet.has(state.activePath)) {
          openFile(state.activePath);
        }
        const pulled = await aheadSummary(result);
        toast(updateMessage(result, pulled), result.updated && result.changed ? 'success' : undefined);
      }
    } catch (err) {
      if (load.active) toast(`Update failed: ${err.message}`, 'error');
    } finally {
      // The button belongs to this invocation, so always restore it.
      btn.disabled = false;
      btn.textContent = original;
      busyDepth -= 1;
    }
  }

  /* ---------------------------------------------------------------- */
  /* Background polling for upstream updates                           */
  /* ---------------------------------------------------------------- */

  /**
   * One poll tick: peek at the upstream and, if the current branch's remote tip
   * has moved, auto-fetch it. Wired to the poller's interval (and exposed as
   * `window.gitBrowser.pollNow` for tests). Stays silent unless there's actually
   * something new; never disturbs an in-flight user action.
   */
  async function pollForUpdates() {
    const source = state.source;
    if (!source || busyDepth > 0) return;
    if (!capabilitiesOf(source).fetch || typeof source.checkForUpdates !== 'function') return;

    let peek;
    try {
      peek = await source.checkForUpdates();
    } catch {
      return; // a transient peek failure; try again next tick, quietly
    }
    // Bail if the world moved under us while we were on the network.
    if (state.source !== source || busyDepth > 0) return;
    if (!peek || !peek.hasUpdates) return;

    await autoUpdate();
  }

  /**
   * Fetch the new commits the peek found, refresh the view, and toast the count.
   * Uses the shared load token so a user action started mid-fetch supersedes the
   * automatic refresh (the fetched objects still land locally regardless).
   */
  async function autoUpdate() {
    const source = state.source;
    const load = loads.begin();
    try {
      const result = await source.update();
      if (!load.active) return;
      await refreshRepo(load);
      if (!load.active) return;
      if (state.activePath && state.fileSet.has(state.activePath)) {
        openFile(state.activePath);
      }
      if (result && result.updated && result.changed) {
        const pulled = await aheadSummary(result);
        if (load.active) toast(autoUpdateMessage(pulled), 'success');
      }
    } catch {
      // A background fetch failure is non-fatal and intentionally silent; the
      // manual Pull / Update button surfaces errors when the user asks for them.
    }
  }

  function autoUpdateMessage(pulled) {
    return pulled ? `${pulled} fetched from the remote.` : 'Fetched new commits from the remote.';
  }

  /** How many commits the fetch brought in, as a phrase ('' when none/unknown). */
  async function aheadSummary(result) {
    if (!result || !result.updated || !result.changed) return '';
    try {
      const recent = await state.source.log(100);
      return newCommitsPhrase(countNewCommits(recent, result.oldOid));
    } catch {
      return '';
    }
  }

  function updateMessage(result, pulled) {
    if (!result || result.updated === false) {
      return 'Demo data is static — nothing to update.';
    }
    if (!result.changed) return 'Already up to date.';
    return pulled ? `${pulled} pulled from the remote.` : 'Updated from remote.';
  }

  /* ---------------------------------------------------------------- */
  /* Open a file (coordinates palette + tree + viewer)                 */
  /* ---------------------------------------------------------------- */

  /**
   * Open a file in the viewer.
   *
   * @param {string} path
   * @param {{lines?: ?{start:number, end:number}}} [opts]  optional line target
   */
  async function openFile(path, opts = {}) {
    palette.close();
    const view = viewLoads.begin();
    const lines = opts.lines || null;

    // reveal in tree
    store.update((s) => {
      s.activePath = path;
      s.lines = lines;
      for (const dir of ancestors(path)) s.expanded.add(dir);
    });
    tree.renderSidebar();

    viewer.beginLoading(path);

    // Classify the entry first so we can show a clear notice for things that
    // aren't ordinary blobs (symlinks, submodules) instead of rendering garbage.
    let meta = null;
    if (typeof state.source.entryMeta === 'function') {
      try {
        meta = await state.source.entryMeta(path);
      } catch {
        meta = null; // be forgiving: fall back to treating it as a normal file
      }
      if (!view.active) return;
    }

    // A submodule is a gitlink with no blob in this clone — there's nothing to
    // read, so render its notice straight away.
    if (meta && meta.kind === 'submodule') {
      viewer.renderSubmodule(path, meta);
      syncHash();
      return;
    }

    let bytes;
    try {
      bytes = await state.source.readFile(path);
    } catch (err) {
      if (view.active) viewer.showReadError(err.message);
      return;
    }

    if (!view.active) return; // a newer open / diff superseded this one
    viewer.render(path, bytes, { lines, meta });
    syncHash();
  }

  /* ---------------------------------------------------------------- */
  /* Diff view                                                         */
  /* ---------------------------------------------------------------- */

  /** Show a commit's changes (against its first parent, or the empty tree). */
  function showCommitDiff(commit) {
    const parent = commit.parent && commit.parent[0];
    return showDiff({
      title: `Changes in ${shortOid(commit.oid)}`,
      subtitle: commitSummary(commit.message),
      baseRef: parent ? { type: 'commit', name: parent } : null,
      headRef: { type: 'commit', name: commit.oid },
    });
  }

  /** Compare two refs (branch/tag/commit) directly. */
  function showCompare(baseRef, headRef) {
    return showDiff({
      title: `Compare ${refLabel(baseRef)} \u2192 ${refLabel(headRef)}`,
      subtitle: '',
      baseRef,
      headRef,
    });
  }

  async function showDiff({ title, subtitle, baseRef, headRef }) {
    if (!state.source || typeof state.source.changedFiles !== 'function') {
      toast('Diffs are not supported for this source.', 'error');
      return;
    }
    palette.close();
    // A diff isn't a file selection; clear the active file highlight and drop
    // the file/lines from the URL (diffs aren't deep-linked).
    store.setState({ activePath: null, lines: null });
    tree.renderSidebar();
    syncHash();

    const view = viewLoads.begin();
    viewer.showDiffLoading(title, subtitle);

    let changes;
    try {
      changes = await state.source.changedFiles(baseRef, headRef);
    } catch (err) {
      if (view.active) viewer.showReadError(err.message);
      return;
    }
    if (!view.active) return;

    viewer.renderDiff({
      title,
      subtitle,
      changes,
      loadFileDiff: (change) => loadFileDiff(change, baseRef, headRef),
    });
  }

  /** Read both sides of a changed file and produce its line diff. */
  async function loadFileDiff(change, baseRef, headRef) {
    let oldBytes = new Uint8Array(0);
    let newBytes = new Uint8Array(0);
    if (change.status !== 'added') oldBytes = await state.source.readFile(change.path, baseRef);
    if (change.status !== 'removed') newBytes = await state.source.readFile(change.path, headRef);
    if (isBinaryExtension(change.path) || looksBinary(oldBytes) || looksBinary(newBytes)) {
      return { binary: true };
    }
    return diffLines(decoder.decode(oldBytes), decoder.decode(newBytes));
  }

  /* ---------------------------------------------------------------- */
  /* Blame view                                                        */
  /* ---------------------------------------------------------------- */

  /** Show per-line blame for a file: each line annotated with its last commit. */
  async function showBlame(path) {
    if (!state.source || typeof state.source.blame !== 'function') {
      toast('Blame is not supported for this source.', 'error');
      return;
    }
    const view = viewLoads.begin();
    viewer.showBlameLoading(path);

    let rows;
    try {
      rows = await state.source.blame(path);
    } catch (err) {
      if (view.active) viewer.showReadError(err.message);
      return;
    }
    if (!view.active) return; // a newer open / diff / blame superseded this one

    if (!rows || !rows.length) {
      // The source supports blame in general but has no per-commit history for
      // this file (e.g. the demo only annotates a sample file). Fall back to the
      // file itself rather than leaving a blank view.
      toast('Blame isn\u2019t available for this file.');
      openFile(path);
      return;
    }
    viewer.renderBlame(path, rows, { onOpenCommit: showCommitDiff });
  }

  /* ---------------------------------------------------------------- */
  /* Deep links / URL hash                                             */
  /* ---------------------------------------------------------------- */

  /** The shareable view state for what's currently on screen, or null. */
  function currentHashState() {
    if (!state.source) return null;
    const hashState = { repo: state.source.url || 'demo', ref: refValue(currentRef()) };
    if (state.activePath) {
      hashState.file = state.activePath;
      if (state.lines) hashState.lines = state.lines;
    }
    return hashState;
  }

  /**
   * Reflect the current view in `location.hash`. No-ops while a deep link is
   * being applied (so intermediate steps don't pollute history) and whenever the
   * URL already matches, so our own writes don't echo back through hashchange.
   */
  function syncHash({ replace = false } = {}) {
    if (restoring) return;
    const hashState = currentHashState();
    saveLastSession(hashState);
    const next = encodeHashState(hashState);
    const inUrl = location.hash.replace(/^#/, '');
    lastHash = next;
    if (next === inUrl) return;
    if (replace) {
      const base = location.pathname + location.search;
      history.replaceState(null, '', next ? `${base}#${next}` : base);
    } else if (next) {
      location.hash = next; // a normal navigation step (adds a history entry)
    } else {
      history.replaceState(null, '', location.pathname + location.search);
    }
  }

  function onHashChange() {
    const inUrl = location.hash.replace(/^#/, '');
    if (inUrl === (lastHash || '')) return; // our own write, ignore
    lastHash = inUrl;
    applyDeepLink(parseHash(location.hash));
  }

  /**
   * Remember the current view so a later visit to the bare URL can reopen it.
   * The demo is intentionally not remembered — it's a one-off "try it", not a
   * session worth restoring on top of the clone screen.
   */
  function saveLastSession(hashState) {
    try {
      if (hashState && hashState.repo && hashState.repo !== 'demo') {
        localStorage.setItem(LAST_SESSION_KEY, JSON.stringify(hashState));
      }
    } catch {
      /* storage may be unavailable; remembering is best-effort */
    }
  }

  /** The remembered session from a previous visit, or null. */
  function loadLastSession() {
    try {
      const raw = localStorage.getItem(LAST_SESSION_KEY);
      const parsed = raw ? JSON.parse(raw) : null;
      return parsed && parsed.repo ? parsed : null;
    } catch {
      return null;
    }
  }

  /** Forget the remembered session (e.g. the user explicitly closed the repo). */
  function clearLastSession() {
    try {
      localStorage.removeItem(LAST_SESSION_KEY);
    } catch {
      /* non-fatal */
    }
  }

  /** Open the repo/ref/file described by a parsed hash state. */
  async function applyDeepLink(parsed) {
    if (!parsed || restoring) return;
    restoring = true;
    try {
      // 1. Make sure the right repository is open.
      const openRepo = state.source ? state.source.url || 'demo' : null;
      if (openRepo !== parsed.repo) {
        const opened = await openForDeepLink(parsed.repo);
        if (!opened) return; // couldn't open here (e.g. not cloned); URL prefilled
      }
      // 2. Switch to the requested ref if needed (quietly — no "Switched to…").
      const targetRef = parsed.ref ? parseRefValue(parsed.ref) : null;
      if (targetRef && refValue(currentRef()) !== refValue(targetRef)) {
        await switchRef(targetRef, { quiet: true });
      }
      // 3. Open the file and apply the line selection.
      if (parsed.file && state.fileSet.has(parsed.file)) {
        await openFile(parsed.file, { lines: parsed.lines || null });
      } else if (parsed.lines && viewer.currentTextPath() === parsed.file) {
        viewer.applyLineSelection(parsed.lines, { scroll: true });
      }
    } finally {
      restoring = false;
      // Canonicalize the hash to what actually loaded (e.g. a missing file is
      // dropped), but only when a repo is open so a prefilled URL stays linkable.
      // Replace (don't push) so restoring doesn't leave a junk history entry.
      if (state.source) syncHash({ replace: true });
    }
  }

  /**
   * Ensure the repo named by a deep link is the open source. Returns whether a
   * source was opened; when the repo isn't available locally it prefills the
   * clone form instead and returns false.
   */
  async function openForDeepLink(repo) {
    if (repo === 'demo') {
      await openSource(createDemoSource());
      return true;
    }
    if (state.storage) {
      const entry = state.storage.listRepos().find((r) => r.url === repo);
      if (entry) {
        try {
          await openSource(await state.storage.open(entry.dir));
          return true;
        } catch {
          /* fall through to prefilling the form */
        }
      }
    }
    // Not cloned in this browser: land on the start screen with the URL ready.
    showStart();
    dom.urlInput.value = repo;
    toast('Clone this repository to open it.');
    return false;
  }

  /* ---------------------------------------------------------------- */
  /* Demo mode                                                         */
  /* ---------------------------------------------------------------- */

  async function openDemo() {
    await openSource(createDemoSource());
    toast('Loaded demo repository (no network used)', 'success');
  }
}
