import { buildFileTree, flattenVisible } from './fileTree.js';
import { fuzzyFilter, highlightSegments } from './fuzzy.js';
import { ancestors, basename, dirname, normalizePath } from './pathUtils.js';
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

// One-tap sample repositories for the clone screen. Kept small (few files /
// few branches) so a shallow clone over the CORS proxy stays fast on mobile.
const PRESET_REPOS = [
  { label: 'octocat/Hello-World', url: 'https://github.com/octocat/Hello-World', note: 'Tiny GitHub sample' },
  { label: 'octocat/Spoon-Knife', url: 'https://github.com/octocat/Spoon-Knife', note: 'Classic fork demo' },
  { label: 'imjasonh/playground', url: 'https://github.com/imjasonh/playground', note: 'This repo' },
  { label: 'github/gitignore', url: 'https://github.com/github/gitignore', note: 'Lots of small files' },
];

const $ = (id) => document.getElementById(id);

function el(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text != null) node.textContent = text;
  return node;
}

const AUTHOR_KEY = 'git-browser:author';

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
  changesOpen: false,
  editing: false,
  changedPaths: new Set(),
  author: {},
  imageUrl: null,
  paletteIndex: 0,
  paletteRows: [],
};

// The push token is held in memory only for the lifetime of the page; it is
// never written to localStorage or the repo registry.
let pushToken = '';

const decoder = new TextDecoder('utf-8', { fatal: false });

/* ------------------------------------------------------------------ */
/* Bootstrapping                                                       */
/* ------------------------------------------------------------------ */

function cacheDom() {
  const ids = [
    'repo-bar', 'repo-name', 'repo-meta', 'branch-select', 'find-btn',
    'history-btn', 'changes-btn', 'changes-count', 'update-btn', 'close-btn',
    'start-view', 'clone-form',
    'url-input', 'ref-input', 'depth-input', 'allbranches-input', 'proxy-input',
    'clone-btn', 'demo-btn', 'preset-list', 'clone-error', 'clone-progress', 'progress-fill',
    'progress-label', 'recent', 'recent-list', 'browser-view', 'tree-filter',
    'new-file-btn', 'file-tree', 'flat-results', 'tree-empty', 'viewer-head', 'file-path',
    'file-info', 'viewer-actions', 'edit-btn', 'delete-btn', 'viewer-body',
    'viewer-placeholder', 'history-panel',
    'history-branch', 'commit-list', 'changes-panel', 'changes-branch',
    'changes-list', 'changes-empty', 'commit-form', 'author-name', 'author-email',
    'commit-message', 'commit-btn', 'push-section', 'push-username', 'push-token',
    'push-btn', 'palette', 'palette-input',
    'palette-results', 'palette-empty', 'newfile-overlay', 'newfile-input',
    'newfile-error', 'newfile-create', 'newfile-cancel', 'toast',
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
  loadAuthor();

  const { GitStorage } = await import('./gitClient.js').catch(() => ({}));
  if (GitStorage) state.storage = new GitStorage();

  bindEvents();
  renderPresets();
  renderRecent();

  if (location.hash === '#demo') {
    openDemo();
  }

  window.gitBrowser = { openDemo, openSource, state };
}

function bindEvents() {
  dom.cloneForm.addEventListener('submit', onCloneSubmit);
  dom.demoBtn.addEventListener('click', openDemo);
  dom.closeBtn.addEventListener('click', showStart);
  dom.branchSelect.addEventListener('change', onBranchChange);
  dom.updateBtn.addEventListener('click', onUpdate);
  dom.historyBtn.addEventListener('click', toggleHistory);
  dom.changesBtn.addEventListener('click', toggleChanges);
  dom.findBtn.addEventListener('click', openPalette);

  // Editing
  dom.newFileBtn.addEventListener('click', openNewFileModal);
  dom.editBtn.addEventListener('click', enterEditMode);
  dom.deleteBtn.addEventListener('click', deleteActiveFile);
  dom.commitForm.addEventListener('submit', onCommitSubmit);
  dom.pushBtn.addEventListener('click', onPush);
  dom.newfileCreate.addEventListener('click', confirmNewFile);
  dom.newfileCancel.addEventListener('click', closeNewFileModal);
  dom.newfileOverlay.addEventListener('click', (e) => {
    if (e.target === dom.newfileOverlay) closeNewFileModal();
  });
  dom.newfileInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
      e.preventDefault();
      confirmNewFile();
    } else if (e.key === 'Escape') {
      closeNewFileModal();
    }
  });
  // Debounced: the tree filter rescans every file on each keystroke, which is
  // wasted work on large repos when someone is typing quickly.
  dom.treeFilter.addEventListener('input', debounce(renderSidebar, 90));
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
  state.editing = false;
  state.changedPaths = new Set();
  revokeImage();
  dom.browserView.hidden = true;
  dom.repoBar.hidden = true;
  dom.startView.hidden = false;
  document.body.classList.remove('repo-open');
  closePalette();
  closeHistory();
  closeChanges();
  closeNewFileModal();
  updateChangesBadge(0);
  renderRecent();
}

function showBrowser() {
  dom.startView.hidden = true;
  dom.browserView.hidden = false;
  dom.repoBar.hidden = false;
  document.body.classList.add('repo-open');
}

/* ------------------------------------------------------------------ */
/* Clone / open                                                        */
/* ------------------------------------------------------------------ */

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

// Monotonic token shared by every async load (open / branch switch / update).
// Each load bumps it and re-checks after every await, so a slower in-flight
// load can never overwrite the view produced by a newer one.
let loadToken = 0;

async function openSource(source) {
  state.source = source;
  state.activePath = null;
  state.expanded = new Set();
  state.historyOpen = false;
  state.changesOpen = false;
  state.editing = false;
  state.changedPaths = new Set();
  revokeImage();

  dom.historyPanel.hidden = true;
  dom.historyBtn.setAttribute('aria-pressed', 'false');
  dom.changesPanel.hidden = true;
  dom.changesBtn.setAttribute('aria-pressed', 'false');
  applyEditableUI();

  const token = ++loadToken;
  showBrowser();
  await refreshRepo(token);
  if (token !== loadToken) return;
  showPlaceholder();
}

/** Show or hide every editing affordance based on the source's capabilities. */
function applyEditableUI() {
  const editable = Boolean(state.source) && !state.source.readOnly;
  dom.changesBtn.hidden = !editable;
  dom.newFileBtn.hidden = !editable;
  dom.pushSection.hidden = !(editable && state.source.canPush);
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

  if (state.historyOpen) loadHistory();
  await refreshChanges();
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

  // Switching branches discards uncommitted working-tree edits, so confirm.
  if (state.changedPaths.size > 0) {
    const ok = window.confirm(
      `You have ${state.changedPaths.size} uncommitted change(s). Switching branches will discard them. Continue?`
    );
    if (!ok) {
      // Restore the select to the current branch.
      dom.branchSelect.value = state.source.getCurrentBranch();
      return;
    }
  }

  const token = ++loadToken;
  try {
    state.editing = false;
    await state.source.setBranch(name);
    await refreshRepo(token);
    if (token !== loadToken) return; // a newer switch/update superseded us

    // Re-open the active file on the new branch if it still exists.
    if (state.activePath && state.fileSet.has(state.activePath)) {
      openFile(state.activePath);
    } else {
      state.activePath = null;
      showPlaceholder();
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
    row.setAttribute('role', 'treeitem');
    row.setAttribute('aria-level', String(depth + 1));

    const twisty = el('span', 'twisty');
    twisty.setAttribute('aria-hidden', 'true');
    if (node.type === 'dir') {
      twisty.textContent = '\u203A'; // ›
      const open = state.expanded.has(node.path);
      if (open) row.classList.add('open');
      row.setAttribute('aria-expanded', String(open));
    } else {
      twisty.textContent = '';
    }
    row.appendChild(twisty);

    const icon = el('span', 'node-icon', node.type === 'dir' ? '\u{1F4C1}' : '\u{1F4C4}');
    icon.setAttribute('aria-hidden', 'true');
    row.appendChild(icon);
    row.appendChild(el('span', 'node-name', node.name));

    if (node.type === 'file' && state.changedPaths.has(node.path)) {
      row.classList.add('changed');
      const dot = el('span', 'change-dot');
      dot.setAttribute('aria-hidden', 'true');
      dot.title = 'Uncommitted change';
      row.appendChild(dot);
    }

    if (node.type === 'file' && node.path === state.activePath) {
      row.classList.add('active');
      row.setAttribute('aria-current', 'true');
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
    row.setAttribute('role', 'option');
    if (state.changedPaths.has(result.item)) row.classList.add('changed');
    if (result.item === state.activePath) {
      row.classList.add('active');
      row.setAttribute('aria-selected', 'true');
    }

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
  state.editing = false;
  closePalette();

  // reveal in tree
  for (const dir of ancestors(path)) state.expanded.add(dir);
  renderSidebar();

  dom.viewerHead.hidden = false;
  renderFilePath(path);
  dom.fileInfo.textContent = 'Loading…';
  hideViewerActions();
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
    updateViewerActions('image');
    return;
  }

  const binary = isBinaryExtension(path) || looksBinary(bytes);
  if (binary) {
    renderBinaryNotice(path, bytes, size);
    updateViewerActions('binary');
    return;
  }

  renderText(path, bytes, size);
  updateViewerActions('text');
}

/** Hide the per-file Edit/Delete actions (e.g. while loading or editing). */
function hideViewerActions() {
  dom.viewerActions.hidden = true;
}

/**
 * Show Edit/Delete for editable sources. Editing is offered for text files;
 * deletion is offered for any file (images and binaries included).
 */
function updateViewerActions(kind) {
  const editable = Boolean(state.source) && !state.source.readOnly;
  if (!editable || state.editing) {
    dom.viewerActions.hidden = true;
    return;
  }
  dom.viewerActions.hidden = false;
  dom.editBtn.hidden = kind !== 'text';
  dom.deleteBtn.hidden = false;
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
  if (state.historyOpen) closeChanges();
  dom.historyPanel.hidden = !state.historyOpen;
  dom.historyBtn.setAttribute('aria-pressed', String(state.historyOpen));
  if (state.historyOpen) loadHistory();
}

function closeHistory() {
  state.historyOpen = false;
  dom.historyPanel.hidden = true;
  dom.historyBtn.setAttribute('aria-pressed', 'false');
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
/* Editing: edit / create / delete files                              */
/* ------------------------------------------------------------------ */

function canEditActive() {
  return Boolean(state.source) && !state.source.readOnly && Boolean(state.activePath);
}

async function enterEditMode() {
  if (!canEditActive()) return;
  const path = state.activePath;
  let bytes;
  try {
    bytes = await state.source.readFile(path);
  } catch (err) {
    toast(`Could not open for editing: ${err.message}`, 'error');
    return;
  }
  if (state.activePath !== path) return;
  renderEditor(path, decoder.decode(bytes), { isNew: false });
}

/** Render the in-place editor (a textarea plus Save / Cancel). */
function renderEditor(path, text, { isNew }) {
  state.editing = true;
  hideViewerActions();
  dom.fileInfo.textContent = isNew ? 'New file' : 'Editing…';

  const wrap = el('div', 'editor');
  const bar = el('div', 'editor-bar');
  const save = el('button', 'btn primary small', 'Save');
  save.type = 'button';
  const cancel = el('button', 'btn small ghost', 'Cancel');
  cancel.type = 'button';
  const hint = el('span', 'editor-hint muted', isNew ? 'Saving stages a new file' : 'Saving stages your change');
  bar.append(save, cancel, hint);

  const area = el('textarea', 'editor-area');
  area.value = text;
  area.spellcheck = false;
  area.setAttribute('aria-label', `Edit ${path}`);

  save.addEventListener('click', () => saveEdit(path, area.value, { isNew }));
  cancel.addEventListener('click', () => cancelEdit(path, { isNew }));

  wrap.append(bar, area);
  dom.viewerBody.replaceChildren(wrap);
  area.focus();
}

function cancelEdit(path, { isNew }) {
  state.editing = false;
  if (isNew) {
    state.activePath = null;
    showPlaceholder();
  } else {
    openFile(path);
  }
}

async function saveEdit(path, value, { isNew }) {
  try {
    await state.source.writeFile(path, value);
  } catch (err) {
    toast(`Could not save: ${err.message}`, 'error');
    return;
  }
  state.editing = false;
  toast(`Saved ${basename(path)} (staged)`, 'success');
  if (isNew || !state.fileSet.has(path)) {
    await reloadFileListPreservingExpansion();
  }
  await refreshChanges();
  await openFile(path);
}

async function deleteActiveFile() {
  if (!canEditActive()) return;
  const path = state.activePath;
  if (!window.confirm(`Delete ${path}? The deletion will be staged for commit.`)) return;
  try {
    await state.source.deleteFile(path);
  } catch (err) {
    toast(`Could not delete: ${err.message}`, 'error');
    return;
  }
  toast(`Deleted ${basename(path)} (staged)`);
  state.activePath = null;
  state.editing = false;
  await reloadFileListPreservingExpansion();
  showPlaceholder();
  hideViewerActions();
  await refreshChanges();
}

/** Reload the file list without resetting the user's expanded directories. */
async function reloadFileListPreservingExpansion() {
  const files = await state.source.listFiles();
  state.files = files;
  state.fileSet = new Set(files);
  state.tree = buildFileTree(files);
  renderSidebar();
}

function openNewFileModal() {
  if (!state.source || state.source.readOnly) return;
  dom.newfileError.hidden = true;
  dom.newfileInput.value = '';
  dom.newfileOverlay.hidden = false;
  dom.newfileInput.focus();
}

function closeNewFileModal() {
  dom.newfileOverlay.hidden = true;
}

function confirmNewFile() {
  const clean = normalizePath(dom.newfileInput.value);
  if (!clean) {
    showNewFileError('Enter a file path.');
    return;
  }
  if (state.fileSet.has(clean)) {
    showNewFileError('That file already exists.');
    return;
  }
  closeNewFileModal();
  startNewFileEditor(clean);
}

function showNewFileError(message) {
  dom.newfileError.textContent = message;
  dom.newfileError.hidden = false;
}

/** Open a blank editor for a brand-new path; the file is created on Save. */
function startNewFileEditor(path) {
  state.activePath = path;
  for (const dir of ancestors(path)) state.expanded.add(dir);
  renderSidebar();
  dom.viewerHead.hidden = false;
  renderFilePath(path);
  renderEditor(path, '', { isNew: true });
}

/* ------------------------------------------------------------------ */
/* Changes drawer: status, commit, push                               */
/* ------------------------------------------------------------------ */

function toggleChanges() {
  state.changesOpen = !state.changesOpen;
  if (state.changesOpen) closeHistory();
  dom.changesPanel.hidden = !state.changesOpen;
  dom.changesBtn.setAttribute('aria-pressed', String(state.changesOpen));
  if (state.changesOpen) loadChanges();
}

function closeChanges() {
  state.changesOpen = false;
  dom.changesPanel.hidden = true;
  dom.changesBtn.setAttribute('aria-pressed', 'false');
}

async function loadChanges() {
  if (!state.source) return;
  dom.changesBranch.textContent = state.source.getCurrentBranch();
  if (!dom.authorName.value) dom.authorName.value = state.author.name || '';
  if (!dom.authorEmail.value) dom.authorEmail.value = state.author.email || '';
  dom.pushSection.hidden = !state.source.canPush;
  await refreshChanges();
}

/**
 * Recompute working-tree status, update the badge and dirty markers, and (when
 * the drawer is open) re-render the change list. Safe to call after any edit.
 */
async function refreshChanges() {
  if (!state.source || state.source.readOnly) {
    state.changedPaths = new Set();
    updateChangesBadge(0);
    return;
  }
  let changes = [];
  try {
    changes = await state.source.status();
  } catch {
    changes = [];
  }
  state.changedPaths = new Set(changes.map((c) => c.path));
  updateChangesBadge(changes.length);
  // Reflect dirty markers in the tree / filter list.
  if (!state.editing) renderSidebar();
  if (state.changesOpen) renderChangesList(changes);
}

function renderChangesList(changes) {
  const list = dom.changesList;
  list.replaceChildren();
  dom.changesEmpty.hidden = changes.length > 0;
  dom.commitBtn.disabled = changes.length === 0;

  const labels = { new: 'A', modified: 'M', deleted: 'D' };
  for (const change of changes) {
    const item = el('li', `change-item ${change.status}`);
    const badge = el('span', 'change-badge', labels[change.status] || '?');
    badge.title = change.status;
    badge.setAttribute('aria-label', change.status);
    item.appendChild(badge);

    const name = el('button', 'change-path');
    name.type = 'button';
    name.textContent = change.path;
    if (change.status === 'deleted') {
      name.disabled = true;
    } else {
      name.addEventListener('click', () => openFile(change.path));
    }
    item.appendChild(name);
    list.appendChild(item);
  }
}

function updateChangesBadge(count) {
  if (count > 0) {
    dom.changesCount.textContent = String(count);
    dom.changesCount.hidden = false;
  } else {
    dom.changesCount.textContent = '';
    dom.changesCount.hidden = true;
  }
}

async function onCommitSubmit(event) {
  event.preventDefault();
  if (!state.source || state.source.readOnly) return;

  const message = dom.commitMessage.value.trim();
  if (!message) {
    toast('Enter a commit message.', 'error');
    dom.commitMessage.focus();
    return;
  }
  const author = {
    name: dom.authorName.value.trim() || 'You',
    email: dom.authorEmail.value.trim() || 'you@example.com',
  };
  saveAuthor(author);

  const btn = dom.commitBtn;
  const original = btn.textContent;
  btn.disabled = true;
  btn.textContent = 'Committing…';
  try {
    const { oid } = await state.source.commit({ message, author });
    dom.commitMessage.value = '';
    toast(`Committed ${shortOid(oid)}`, 'success');

    // The file set is unchanged by a commit, so refresh head + history +
    // status in place rather than rebuilding (and collapsing) the tree.
    try {
      renderHead(await state.source.headCommit());
    } catch {
      /* leave the header as-is */
    }
    if (state.historyOpen) await loadHistory();
    await refreshChanges();
    if (state.activePath && state.fileSet.has(state.activePath) && !state.editing) {
      openFile(state.activePath);
    }
  } catch (err) {
    toast(`Commit failed: ${err.message}`, 'error');
  } finally {
    btn.textContent = original;
    btn.disabled = state.changedPaths.size === 0;
  }
}

async function onPush() {
  if (!state.source || !state.source.canPush) return;
  const token = dom.pushToken.value.trim();
  const username = dom.pushUsername.value.trim();
  if (!token) {
    toast('Enter a token to push.', 'error');
    dom.pushToken.focus();
    return;
  }
  pushToken = token; // session-only

  const btn = dom.pushBtn;
  const original = btn.textContent;
  btn.disabled = true;
  btn.textContent = 'Pushing…';
  try {
    await state.source.push({
      token,
      username: username || undefined,
      onProgress: (p) => {
        btn.textContent = p && p.phase ? `${p.phase}…` : 'Pushing…';
      },
    });
    toast('Pushed to remote.', 'success');
  } catch (err) {
    toast(`Push failed: ${pushErrorMessage(err)}`, 'error');
  } finally {
    btn.disabled = false;
    btn.textContent = original;
  }
}

function pushErrorMessage(err) {
  const message = (err && err.message) || String(err);
  if (/401|403|auth|credential|denied|permission/i.test(message)) {
    return `Authentication failed — check your token and its scopes. (${message})`;
  }
  if (/non-fast-forward|fetch first|rejected/i.test(message)) {
    return `Remote has newer commits — Pull / Update first, then push. (${message})`;
  }
  if (/Failed to fetch|NetworkError|CORS/i.test(message)) {
    return `Could not reach the remote (CORS proxy or network). (${message})`;
  }
  return message;
}

function loadAuthor() {
  try {
    const parsed = JSON.parse(localStorage.getItem(AUTHOR_KEY));
    state.author = parsed && typeof parsed === 'object' ? parsed : {};
  } catch {
    state.author = {};
  }
}

function saveAuthor(author) {
  state.author = { name: author.name, email: author.email };
  try {
    localStorage.setItem(AUTHOR_KEY, JSON.stringify(state.author));
  } catch {
    /* storage may be unavailable; non-fatal */
  }
}

/* ------------------------------------------------------------------ */
/* Command palette (fuzzy finder)                                      */
/* ------------------------------------------------------------------ */

let paletteReturnFocus = null;

function openPalette() {
  if (!state.source) return;
  paletteReturnFocus = document.activeElement;
  dom.palette.hidden = false;
  dom.paletteInput.value = '';
  dom.paletteInput.focus();
  renderPalette();
}

function closePalette() {
  const wasOpen = !dom.palette.hidden;
  dom.palette.hidden = true;
  // Return focus to whatever opened the palette so keyboard users aren't
  // dumped back at the top of the document.
  if (
    wasOpen &&
    paletteReturnFocus &&
    typeof paletteReturnFocus.focus === 'function' &&
    document.contains(paletteReturnFocus)
  ) {
    paletteReturnFocus.focus();
  }
  paletteReturnFocus = null;
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
  } else if (event.key === 'Escape' && !dom.newfileOverlay.hidden) {
    closeNewFileModal();
  }
}

/* ------------------------------------------------------------------ */
/* Recent repositories                                                 */
/* ------------------------------------------------------------------ */

function renderPresets() {
  dom.presetList.replaceChildren();
  for (const preset of PRESET_REPOS) {
    const button = el('button', 'preset');
    button.type = 'button';
    button.appendChild(el('span', 'p-name', preset.label));
    if (preset.note) button.appendChild(el('span', 'p-note', preset.note));
    button.addEventListener('click', () => {
      dom.urlInput.value = preset.url;
      if (preset.ref) dom.refInput.value = preset.ref;
      startClone();
    });
    dom.presetList.appendChild(button);
  }
}

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

function debounce(fn, ms) {
  let timer = null;
  return (...args) => {
    clearTimeout(timer);
    timer = setTimeout(() => fn(...args), ms);
  };
}

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
  dom.demoBtn.disabled = busy;
  for (const button of dom.presetList.querySelectorAll('button')) {
    button.disabled = busy;
  }
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
