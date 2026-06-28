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
import { createHistory } from './ui/history.js';
import { createRecent } from './ui/recent.js';
import { buildFileTree } from './fileTree.js';
import { ancestors } from './pathUtils.js';
import { parseRepoUrl, DEFAULT_CORS_PROXY } from './repoUrl.js';
import { commitSummary, shortOid } from './format.js';
import { createDemoSource } from './demoRepo.js';

// Every element id the UI looks up. Kept in one list so the static wiring test
// can confirm each one exists in index.html.
const DOM_IDS = [
  'repo-bar', 'repo-name', 'repo-meta', 'branch-select', 'find-btn',
  'history-btn', 'update-btn', 'close-btn', 'start-view', 'clone-form',
  'url-input', 'ref-input', 'depth-input', 'allbranches-input', 'proxy-input',
  'clone-btn', 'demo-btn', 'preset-list', 'clone-error', 'clone-progress', 'progress-fill',
  'progress-label', 'recent', 'recent-list', 'browser-view', 'tree-filter',
  'file-tree', 'flat-results', 'tree-empty', 'viewer-head', 'file-path',
  'file-info', 'viewer-body', 'viewer-placeholder', 'history-panel',
  'history-branch', 'commit-list', 'palette', 'palette-input',
  'palette-results', 'palette-empty', 'toast',
];

export async function init() {
  const dom = cacheDom(DOM_IDS);
  const feedback = createFeedback(dom);
  const { toast, hideToast, showProgress, hideProgress, showError, hideError } = feedback;

  const state = {
    storage: null,
    source: null,
    files: [],
    fileSet: new Set(),
    tree: null,
    expanded: new Set(),
    activePath: null,
    branches: [],
    historyOpen: false,
  };

  // Monotonic token shared by every async load (open / branch switch / update).
  // Each load bumps it and re-checks after every await, so a slower in-flight
  // load can never overwrite the view produced by a newer one.
  let loadToken = 0;

  // The shared context handed to each UI module. Cross-module actions are
  // assigned below, after the modules exist; modules only call them at
  // event time, so the late binding is safe.
  const ctx = { state, dom, toast, hideToast };

  const viewer = createViewer(ctx);
  const tree = createTree(ctx);
  const palette = createPalette(ctx);
  const history = createHistory(ctx);
  const recent = createRecent(ctx);

  ctx.openFile = openFile;
  ctx.openSource = openSource;
  ctx.startClone = startClone;

  dom.proxyInput.value = DEFAULT_CORS_PROXY;

  const { GitStorage } = await import('./gitClient.js').catch(() => ({}));
  if (GitStorage) state.storage = new GitStorage();

  bindEvents();
  recent.renderPresets();
  recent.renderRecent();

  if (location.hash === '#demo') {
    openDemo();
  }

  window.gitBrowser = { openDemo, openSource, state };

  /* ---------------------------------------------------------------- */
  /* Event wiring                                                      */
  /* ---------------------------------------------------------------- */

  function bindEvents() {
    dom.cloneForm.addEventListener('submit', onCloneSubmit);
    dom.demoBtn.addEventListener('click', openDemo);
    dom.closeBtn.addEventListener('click', showStart);
    dom.branchSelect.addEventListener('change', onBranchChange);
    dom.updateBtn.addEventListener('click', onUpdate);
    dom.historyBtn.addEventListener('click', () => history.toggle());
    dom.findBtn.addEventListener('click', () => palette.open());
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
    const isFind = (event.metaKey || event.ctrlKey) && event.key.toLowerCase() === 'p';
    if (isFind && state.source) {
      event.preventDefault();
      if (palette.isOpen()) palette.close();
      else palette.open();
      return;
    }
    if (event.key === 'Escape' && palette.isOpen()) {
      palette.close();
    }
  }

  /* ---------------------------------------------------------------- */
  /* View switching                                                    */
  /* ---------------------------------------------------------------- */

  function showStart() {
    state.source = null;
    state.activePath = null;
    viewer.dispose();
    dom.browserView.hidden = true;
    dom.repoBar.hidden = true;
    dom.startView.hidden = false;
    document.body.classList.remove('repo-open');
    palette.close();
    recent.renderRecent();
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

  function cloneErrorMessage(err, corsProxy) {
    const message = (err && err.message) || String(err);
    if (/Failed to fetch|NetworkError|CORS|ENOTFOUND/i.test(message)) {
      return corsProxy
        ? `Could not reach the repository. The CORS proxy may be down or the URL may be wrong. (${message})`
        : `Could not reach the repository. Most hosts need a CORS proxy — set one in Advanced options. (${message})`;
    }
    if (/404|not found|Could not find/i.test(message)) {
      return `Repository or ref not found. Check the URL and branch. (${message})`;
    }
    return `Clone failed: ${message}`;
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
    state.source = source;
    state.activePath = null;
    state.expanded = new Set();
    viewer.dispose();
    history.reset();

    const token = ++loadToken;
    showBrowser();
    tree.resetScroll();
    await refreshRepo(token);
    if (token !== loadToken) return;
    viewer.showPlaceholder();
  }

  /** Reload branch list, files, and header for the current branch. */
  async function refreshRepo(token) {
    const source = state.source;
    dom.repoName.textContent = source.fullName;

    const branches = await source.listBranches();
    if (token !== loadToken) return;
    state.branches = branches;
    renderBranchSelect();

    await reloadFiles(token);
    if (token !== loadToken) return;

    try {
      const head = await source.headCommit();
      if (token !== loadToken) return;
      renderHead(head);
    } catch {
      dom.repoMeta.textContent = '';
    }

    if (state.historyOpen) history.load();
  }

  async function reloadFiles(token) {
    const files = await state.source.listFiles();
    if (token !== loadToken) return;
    state.files = files;
    state.fileSet = new Set(files);
    state.tree = buildFileTree(files);
    // Auto-expand a single top-level directory chain for convenience.
    state.expanded = new Set();
    autoExpand();
    dom.treeFilter.value = '';
    tree.renderSidebar();
  }

  function autoExpand() {
    let nodes = state.tree.children;
    // expand while there is exactly one directory at this level
    while (nodes.length === 1 && nodes[0].type === 'dir') {
      state.expanded.add(nodes[0].path);
      nodes = nodes[0].children;
    }
  }

  function renderHead(head) {
    if (!head) {
      dom.repoMeta.textContent = `${state.files.length} files`;
      return;
    }
    dom.repoMeta.textContent =
      `${state.source.getCurrentBranch()} · ${shortOid(head.oid)} · ` +
      `${commitSummary(head.message)} · ${state.files.length} files`;
  }

  function renderBranchSelect() {
    const select = dom.branchSelect;
    select.replaceChildren();
    const current = state.source.getCurrentBranch();
    for (const branch of state.branches) {
      const option = el('option', null, branch.name);
      option.value = branch.name;
      if (branch.name === current) option.selected = true;
      select.appendChild(option);
    }
    select.disabled = state.branches.length <= 1;
  }

  async function onBranchChange() {
    const name = dom.branchSelect.value;
    const token = ++loadToken;
    try {
      await state.source.setBranch(name);
      await refreshRepo(token);
      if (token !== loadToken) return; // a newer switch/update superseded us

      // Re-open the active file on the new branch if it still exists.
      if (state.activePath && state.fileSet.has(state.activePath)) {
        openFile(state.activePath);
      } else {
        state.activePath = null;
        viewer.showPlaceholder();
      }
      toast(`Switched to ${name}`);
    } catch (err) {
      if (token === loadToken) toast(`Could not switch branch: ${err.message}`, 'error');
    }
  }

  async function onUpdate() {
    if (!state.source) return;
    const token = ++loadToken;
    const btn = dom.updateBtn;
    btn.disabled = true;
    const original = btn.textContent;
    btn.textContent = 'Updating…';
    try {
      const result = await state.source.update((p) => {
        btn.textContent = p.phase ? `${p.phase}…` : 'Updating…';
      });
      await refreshRepo(token);
      if (token === loadToken) {
        if (state.activePath && state.fileSet.has(state.activePath)) {
          openFile(state.activePath);
        }
        toast(updateMessage(result), result.updated && result.changed ? 'success' : undefined);
      }
    } catch (err) {
      if (token === loadToken) toast(`Update failed: ${err.message}`, 'error');
    } finally {
      // The button belongs to this invocation, so always restore it.
      btn.disabled = false;
      btn.textContent = original;
    }
  }

  function updateMessage(result) {
    if (!result || result.updated === false) {
      return 'Demo data is static — nothing to update.';
    }
    return result.changed ? 'Updated from remote.' : 'Already up to date.';
  }

  /* ---------------------------------------------------------------- */
  /* Open a file (coordinates palette + tree + viewer)                 */
  /* ---------------------------------------------------------------- */

  async function openFile(path) {
    state.activePath = path;
    palette.close();

    // reveal in tree
    for (const dir of ancestors(path)) state.expanded.add(dir);
    tree.renderSidebar();

    viewer.beginLoading(path);

    let bytes;
    try {
      bytes = await state.source.readFile(path);
    } catch (err) {
      viewer.showReadError(err.message);
      return;
    }

    if (state.activePath !== path) return; // a newer open superseded this one
    viewer.render(path, bytes);
  }

  /* ---------------------------------------------------------------- */
  /* Demo mode                                                         */
  /* ---------------------------------------------------------------- */

  async function openDemo() {
    await openSource(createDemoSource());
    toast('Loaded demo repository (no network used)', 'success');
  }
}
