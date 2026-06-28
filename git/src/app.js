import { buildFileTree, flattenVisible } from './fileTree.js';
import { fuzzyFilter, highlightSegments } from './fuzzy.js';
import { ancestors, basename, dirname } from './pathUtils.js';
import { parseRepoUrl, DEFAULT_CORS_PROXY } from './repoUrl.js';
import {
  imageMimeType,
  isImagePath,
  isBinaryExtension,
  languageForPath,
  looksBinary,
} from './language.js';
import { commitSummary, formatBytes, relativeTime, shortOid } from './format.js';
import { createDemoSource } from './demoRepo.js';

const MAX_TEXT_BYTES = 2_000_000;
const MAX_TEXT_LINES = 50_000;
const PALETTE_LIMIT = 60;
const FILTER_LIMIT = 400;

const $ = (id) => document.getElementById(id);

function el(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text != null) node.textContent = text;
  return node;
}

const dom = {};
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
  imageUrl: null,
  paletteIndex: 0,
  paletteRows: [],
};

const decoder = new TextDecoder('utf-8', { fatal: false });

/* ------------------------------------------------------------------ */
/* Bootstrapping                                                       */
/* ------------------------------------------------------------------ */

function cacheDom() {
  const ids = [
    'repo-bar', 'repo-name', 'repo-meta', 'branch-select', 'find-btn',
    'history-btn', 'update-btn', 'close-btn', 'start-view', 'clone-form',
    'url-input', 'ref-input', 'depth-input', 'allbranches-input', 'proxy-input',
    'clone-btn', 'demo-btn', 'clone-error', 'clone-progress', 'progress-fill',
    'progress-label', 'recent', 'recent-list', 'browser-view', 'tree-filter',
    'file-tree', 'flat-results', 'tree-empty', 'viewer-head', 'file-path',
    'file-info', 'viewer-body', 'viewer-placeholder', 'history-panel',
    'history-branch', 'commit-list', 'palette', 'palette-input',
    'palette-results', 'palette-empty', 'toast',
  ];
  for (const id of ids) {
    dom[camel(id)] = $(id);
  }
}

function camel(id) {
  return id.replace(/-([a-z])/g, (_, c) => c.toUpperCase());
}

async function init() {
  cacheDom();
  dom.proxyInput.value = DEFAULT_CORS_PROXY;

  const { GitStorage } = await import('./gitClient.js').catch(() => ({}));
  if (GitStorage) state.storage = new GitStorage();

  bindEvents();
  renderRecent();

  if (location.hash === '#demo') {
    openDemo();
  }

  window.gitBrowser = { openDemo, openSource, state };
}

function bindEvents() {
  dom.cloneForm.addEventListener('submit', onClone);
  dom.demoBtn.addEventListener('click', openDemo);
  dom.closeBtn.addEventListener('click', showStart);
  dom.branchSelect.addEventListener('change', onBranchChange);
  dom.updateBtn.addEventListener('click', onUpdate);
  dom.historyBtn.addEventListener('click', toggleHistory);
  dom.findBtn.addEventListener('click', openPalette);
  dom.treeFilter.addEventListener('input', renderSidebar);
  dom.paletteInput.addEventListener('input', renderPalette);

  document.addEventListener('keydown', onGlobalKey);
  dom.palette.addEventListener('click', (e) => {
    if (e.target === dom.palette) closePalette();
  });
  dom.paletteInput.addEventListener('keydown', onPaletteKey);
}

/* ------------------------------------------------------------------ */
/* View switching                                                      */
/* ------------------------------------------------------------------ */

function showStart() {
  state.source = null;
  state.activePath = null;
  revokeImage();
  dom.browserView.hidden = true;
  dom.repoBar.hidden = true;
  dom.startView.hidden = false;
  closePalette();
  renderRecent();
}

function showBrowser() {
  dom.startView.hidden = true;
  dom.browserView.hidden = false;
  dom.repoBar.hidden = false;
}

/* ------------------------------------------------------------------ */
/* Clone / open                                                        */
/* ------------------------------------------------------------------ */

async function onClone(event) {
  event.preventDefault();
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

async function openSource(source) {
  state.source = source;
  state.activePath = null;
  state.expanded = new Set();
  state.historyOpen = false;
  revokeImage();

  dom.historyPanel.hidden = true;
  dom.historyBtn.setAttribute('aria-pressed', 'false');

  showBrowser();
  await refreshRepo();
  showPlaceholder();
}

/** Reload branch list, files, and header for the current branch. */
async function refreshRepo() {
  const source = state.source;
  dom.repoName.textContent = source.fullName;

  state.branches = await source.listBranches();
  renderBranchSelect();

  await reloadFiles();

  try {
    const head = await source.headCommit();
    renderHead(head);
  } catch {
    dom.repoMeta.textContent = '';
  }

  if (state.historyOpen) loadHistory();
}

async function reloadFiles() {
  const files = await state.source.listFiles();
  state.files = files;
  state.fileSet = new Set(files);
  state.tree = buildFileTree(files);
  // Auto-expand a single top-level directory chain for convenience.
  state.expanded = new Set();
  autoExpand();
  dom.treeFilter.value = '';
  renderSidebar();
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
  try {
    await state.source.setBranch(name);
    await reloadFiles();
    const head = await state.source.headCommit().catch(() => null);
    renderHead(head);
    if (state.historyOpen) loadHistory();

    // Re-open the active file on the new branch if it still exists.
    if (state.activePath && state.fileSet.has(state.activePath)) {
      openFile(state.activePath);
    } else {
      state.activePath = null;
      showPlaceholder();
    }
    toast(`Switched to ${name}`);
  } catch (err) {
    toast(`Could not switch branch: ${err.message}`, 'error');
  }
}

async function onUpdate() {
  if (!state.source) return;
  const btn = dom.updateBtn;
  btn.disabled = true;
  const original = btn.textContent;
  btn.textContent = 'Updating…';
  try {
    const result = await state.source.update((p) => {
      btn.textContent = p.phase ? `${p.phase}…` : 'Updating…';
    });
    await refreshRepo();
    if (state.activePath && state.fileSet.has(state.activePath)) {
      openFile(state.activePath);
    }
    toast(result.updated === false ? 'Demo data is static — nothing to update.' : 'Updated from remote.', result.updated === false ? undefined : 'success');
  } catch (err) {
    toast(`Update failed: ${err.message}`, 'error');
  } finally {
    btn.disabled = false;
    btn.textContent = original;
  }
}

/* ------------------------------------------------------------------ */
/* Sidebar: tree + quick filter                                        */
/* ------------------------------------------------------------------ */

function renderSidebar() {
  const query = dom.treeFilter.value.trim();
  if (query) {
    renderFlatResults(query);
  } else {
    dom.flatResults.hidden = true;
    dom.fileTree.hidden = false;
    renderTree();
  }
}

function renderTree() {
  const rows = flattenVisible(state.tree, state.expanded);
  const list = dom.fileTree;
  list.replaceChildren();
  dom.treeEmpty.hidden = rows.length > 0;

  for (const { node, depth } of rows) {
    const row = el('button', 'tree-row');
    row.type = 'button';
    row.style.paddingLeft = `${0.4 + depth * 0.85}rem`;
    row.dataset.path = node.path;

    const twisty = el('span', 'twisty');
    if (node.type === 'dir') {
      twisty.textContent = '\u203A'; // ›
      if (state.expanded.has(node.path)) row.classList.add('open');
    } else {
      twisty.textContent = '';
    }
    row.appendChild(twisty);

    row.appendChild(el('span', 'node-icon', node.type === 'dir' ? '\u{1F4C1}' : '\u{1F4C4}'));
    row.appendChild(el('span', 'node-name', node.name));

    if (node.type === 'file' && node.path === state.activePath) {
      row.classList.add('active');
    }

    row.addEventListener('click', () => {
      if (node.type === 'dir') {
        toggleDir(node.path);
      } else {
        openFile(node.path);
      }
    });
    list.appendChild(row);
  }
}

function toggleDir(path) {
  if (state.expanded.has(path)) state.expanded.delete(path);
  else state.expanded.add(path);
  renderTree();
}

function renderFlatResults(query) {
  dom.fileTree.hidden = true;
  const list = dom.flatResults;
  list.hidden = false;
  list.replaceChildren();

  const results = fuzzyFilter(query, state.files, { limit: FILTER_LIMIT });
  dom.treeEmpty.hidden = results.length > 0;

  for (const result of results) {
    const row = el('li', 'flat-row');
    row.dataset.path = result.item;
    if (result.item === state.activePath) row.classList.add('active');

    const nameStart = result.target.length - basename(result.target).length;
    const namePositions = result.positions
      .filter((p) => p >= nameStart)
      .map((p) => p - nameStart);
    row.appendChild(highlightedSpan('fr-name', basename(result.item), namePositions));
    row.appendChild(highlightedSpan('fr-path', result.item, result.positions));

    row.addEventListener('click', () => openFile(result.item));
    list.appendChild(row);
  }
}

function highlightedSpan(className, text, positions) {
  const span = el('span', className);
  for (const segment of highlightSegments(text, positions)) {
    span.appendChild(el('span', segment.match ? 'match' : null, segment.text));
  }
  return span;
}

/* ------------------------------------------------------------------ */
/* File viewer                                                         */
/* ------------------------------------------------------------------ */

function showPlaceholder() {
  dom.viewerHead.hidden = true;
  dom.viewerBody.replaceChildren(dom.viewerPlaceholder);
  dom.viewerPlaceholder.hidden = false;
}

async function openFile(path) {
  state.activePath = path;
  closePalette();

  // reveal in tree
  for (const dir of ancestors(path)) state.expanded.add(dir);
  renderSidebar();

  dom.viewerHead.hidden = false;
  renderFilePath(path);
  dom.fileInfo.textContent = 'Loading…';
  dom.viewerBody.replaceChildren(el('div', 'notice', 'Loading…'));

  let bytes;
  try {
    bytes = await state.source.readFile(path);
  } catch (err) {
    dom.viewerBody.replaceChildren(el('div', 'notice', `Could not read file: ${err.message}`));
    dom.fileInfo.textContent = '';
    return;
  }

  if (state.activePath !== path) return; // a newer open superseded this one

  const size = bytes.length;
  revokeImage();

  if (isImagePath(path)) {
    renderImage(path, bytes, size);
    return;
  }

  const binary = isBinaryExtension(path) || looksBinary(bytes);
  if (binary) {
    renderBinaryNotice(path, bytes, size);
    return;
  }

  renderText(path, bytes, size);
}

function renderFilePath(path) {
  const dir = dirname(path);
  dom.filePath.replaceChildren();
  if (dir) {
    dom.filePath.appendChild(el('span', 'dir', `${dir}/`));
  }
  dom.filePath.appendChild(el('span', 'name', basename(path)));
}

function renderText(path, bytes, size, { force = false } = {}) {
  const text = decoder.decode(bytes);
  let lines = text.split('\n');
  if (lines.length > 1 && lines[lines.length - 1] === '' && text.endsWith('\n')) {
    lines = lines.slice(0, -1);
  }

  if (!force && (size > MAX_TEXT_BYTES || lines.length > MAX_TEXT_LINES)) {
    dom.fileInfo.textContent = `${languageForPath(path)} · ${formatBytes(size)}`;
    const notice = el('div', 'notice');
    notice.appendChild(el('p', null, `Large file (${formatBytes(size)}, ${lines.length} lines).`));
    const btn = el('button', 'btn', 'Show anyway');
    btn.type = 'button';
    btn.addEventListener('click', () => renderText(path, bytes, size, { force: true }));
    notice.appendChild(btn);
    dom.viewerBody.replaceChildren(notice);
    return;
  }

  dom.fileInfo.textContent =
    `${languageForPath(path)} · ${lines.length} lines · ${formatBytes(size)}`;

  const view = el('div', 'code-view');
  const gutter = el('div', 'gutter');
  gutter.textContent = lines.map((_, i) => i + 1).join('\n');
  const code = el('div', 'code');
  code.textContent = lines.join('\n');
  view.append(gutter, code);
  dom.viewerBody.replaceChildren(view);
}

function renderImage(path, bytes, size) {
  const blob = new Blob([bytes], { type: imageMimeType(path) });
  state.imageUrl = URL.createObjectURL(blob);
  dom.fileInfo.textContent = `Image · ${formatBytes(size)}`;
  const wrap = el('div', 'image-view');
  const img = el('img');
  img.src = state.imageUrl;
  img.alt = path;
  wrap.appendChild(img);
  dom.viewerBody.replaceChildren(wrap);
}

function renderBinaryNotice(path, bytes, size) {
  dom.fileInfo.textContent = `Binary · ${formatBytes(size)}`;
  const notice = el('div', 'notice');
  notice.appendChild(el('p', null, `Binary file — ${formatBytes(size)}.`));
  const btn = el('button', 'btn', 'View as text');
  btn.type = 'button';
  btn.addEventListener('click', () => renderText(path, bytes, size, { force: true }));
  notice.appendChild(btn);
  dom.viewerBody.replaceChildren(notice);
}

function revokeImage() {
  if (state.imageUrl) {
    URL.revokeObjectURL(state.imageUrl);
    state.imageUrl = null;
  }
}

/* ------------------------------------------------------------------ */
/* History                                                             */
/* ------------------------------------------------------------------ */

function toggleHistory() {
  state.historyOpen = !state.historyOpen;
  dom.historyPanel.hidden = !state.historyOpen;
  dom.historyBtn.setAttribute('aria-pressed', String(state.historyOpen));
  if (state.historyOpen) loadHistory();
}

async function loadHistory() {
  if (!state.source) return;
  dom.historyBranch.textContent = state.source.getCurrentBranch();
  dom.commitList.replaceChildren(el('li', 'commit-item muted', 'Loading…'));
  try {
    const commits = await state.source.log(100);
    dom.commitList.replaceChildren();
    if (commits.length === 0) {
      dom.commitList.appendChild(el('li', 'commit-item muted', 'No history.'));
      return;
    }
    for (const commit of commits) {
      const item = el('li', 'commit-item');
      item.appendChild(el('p', 'commit-msg', commitSummary(commit.message)));
      const meta = el('div', 'commit-meta');
      meta.appendChild(el('span', 'commit-oid', shortOid(commit.oid)));
      if (commit.author.name) meta.appendChild(el('span', null, commit.author.name));
      if (commit.timestamp) meta.appendChild(el('span', null, relativeTime(commit.timestamp)));
      item.appendChild(meta);
      dom.commitList.appendChild(item);
    }
  } catch (err) {
    dom.commitList.replaceChildren(el('li', 'commit-item muted', `History unavailable: ${err.message}`));
  }
}

/* ------------------------------------------------------------------ */
/* Command palette (fuzzy finder)                                      */
/* ------------------------------------------------------------------ */

function openPalette() {
  if (!state.source) return;
  dom.palette.hidden = false;
  dom.paletteInput.value = '';
  dom.paletteInput.focus();
  renderPalette();
}

function closePalette() {
  dom.palette.hidden = true;
}

function renderPalette() {
  const query = dom.paletteInput.value.trim();
  const results = fuzzyFilter(query, state.files, { limit: PALETTE_LIMIT });
  state.paletteRows = results;
  state.paletteIndex = 0;

  const list = dom.paletteResults;
  list.replaceChildren();
  dom.paletteEmpty.hidden = results.length > 0;

  results.forEach((result, index) => {
    const row = el('li', 'palette-row');
    row.dataset.path = result.item;
    if (index === 0) row.classList.add('active');

    const nameStart = result.target.length - basename(result.target).length;
    const namePositions = result.positions
      .filter((p) => p >= nameStart)
      .map((p) => p - nameStart);
    row.appendChild(highlightedSpan('pr-name', basename(result.item), namePositions));
    row.appendChild(highlightedSpan('pr-path', result.item, result.positions));

    row.addEventListener('click', () => openFile(result.item));
    list.appendChild(row);
  });
}

function movePalette(delta) {
  const rows = dom.paletteResults.children;
  if (rows.length === 0) return;
  rows[state.paletteIndex]?.classList.remove('active');
  state.paletteIndex = (state.paletteIndex + delta + rows.length) % rows.length;
  const active = rows[state.paletteIndex];
  active.classList.add('active');
  active.scrollIntoView({ block: 'nearest' });
}

function onPaletteKey(event) {
  if (event.key === 'ArrowDown') {
    event.preventDefault();
    movePalette(1);
  } else if (event.key === 'ArrowUp') {
    event.preventDefault();
    movePalette(-1);
  } else if (event.key === 'Enter') {
    event.preventDefault();
    const row = state.paletteRows[state.paletteIndex];
    if (row) openFile(row.item);
  } else if (event.key === 'Escape') {
    event.preventDefault();
    closePalette();
  }
}

function onGlobalKey(event) {
  const isFind = (event.metaKey || event.ctrlKey) && event.key.toLowerCase() === 'p';
  if (isFind && state.source) {
    event.preventDefault();
    if (dom.palette.hidden) openPalette();
    else closePalette();
    return;
  }
  if (event.key === 'Escape' && !dom.palette.hidden) {
    closePalette();
  }
}

/* ------------------------------------------------------------------ */
/* Recent repositories                                                 */
/* ------------------------------------------------------------------ */

function renderRecent() {
  if (!state.storage) {
    dom.recent.hidden = true;
    return;
  }
  const repos = state.storage.listRepos();
  if (repos.length === 0) {
    dom.recent.hidden = true;
    return;
  }
  dom.recent.hidden = false;
  dom.recentList.replaceChildren();

  for (const repo of repos) {
    const item = el('li', 'recent-item');

    const main = el('div', 'ri-main');
    main.appendChild(el('div', 'ri-name', repo.fullName || repo.dir));
    const when = repo.lastUsed ? `opened ${relativeTime(Math.round(repo.lastUsed / 1000))}` : '';
    main.appendChild(el('div', 'ri-meta', [repo.url, when].filter(Boolean).join(' · ')));
    main.addEventListener('click', () => openStored(repo.dir));
    item.appendChild(main);

    const remove = el('button', 'ri-remove', '\u00D7');
    remove.type = 'button';
    remove.title = 'Remove from local storage';
    remove.setAttribute('aria-label', `Remove ${repo.fullName}`);
    remove.addEventListener('click', async (e) => {
      e.stopPropagation();
      try {
        await state.storage.remove(repo.dir);
        renderRecent();
        toast('Removed from local storage');
      } catch (err) {
        toast(`Could not remove: ${err.message}`, 'error');
      }
    });
    item.appendChild(remove);

    dom.recentList.appendChild(item);
  }
}

async function openStored(dir) {
  try {
    toast('Opening…');
    const source = await state.storage.open(dir);
    await openSource(source);
    hideToast();
  } catch (err) {
    toast(`Could not open repository: ${err.message}`, 'error');
  }
}

/* ------------------------------------------------------------------ */
/* Demo mode                                                           */
/* ------------------------------------------------------------------ */

async function openDemo() {
  await openSource(createDemoSource());
  toast('Loaded demo repository (no network used)', 'success');
}

/* ------------------------------------------------------------------ */
/* Small UI helpers                                                    */
/* ------------------------------------------------------------------ */

function showError(message) {
  dom.cloneError.textContent = message;
  dom.cloneError.hidden = false;
}
function hideError() {
  dom.cloneError.hidden = true;
}

function setCloning(busy) {
  dom.cloneBtn.disabled = busy;
  dom.cloneBtn.textContent = busy ? 'Cloning…' : 'Clone';
}

function showProgress(label, pct) {
  dom.cloneProgress.hidden = false;
  if (typeof pct === 'number') {
    dom.progressFill.style.width = `${pct}%`;
  }
  dom.progressLabel.textContent = pct != null ? `${label} ${pct}%` : label;
}
function hideProgress() {
  dom.cloneProgress.hidden = true;
  dom.progressFill.style.width = '0%';
}

let toastTimer = null;
function toast(message, type) {
  dom.toast.textContent = message;
  dom.toast.className = `toast${type ? ` ${type}` : ''}`;
  dom.toast.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(hideToast, 3200);
}
function hideToast() {
  dom.toast.hidden = true;
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
}

export { state };
