/**
 * Read-write editing concern: the in-place file editor, the new-file modal,
 * deletion, and the Changes drawer (working-tree status + commit + push).
 *
 * Everything here is gated on `state.source.readOnly === false`; a read-only
 * source keeps every affordance hidden. The module owns its own changes-drawer
 * open flag, the (session-only) push token, and the remembered commit author,
 * and reaches the rest of the app only through the shared `ctx` callbacks.
 */
import { el } from './dom.js';
import { ancestors, basename, normalizePath } from '../pathUtils.js';
import { buildFileTree } from '../fileTree.js';
import { shortOid } from '../format.js';

const AUTHOR_KEY = 'git-browser:author';

/**
 * @param {{
 *   state: object,
 *   dom: Record<string, HTMLElement>,
 *   toast: Function,
 *   openFile: Function,
 *   renderSidebar: Function,
 *   renderFilePath: Function,
 *   showPlaceholder: Function,
 *   renderHead: Function,
 *   reloadHistory: Function,
 *   closeHistory: Function,
 * }} ctx
 */
export function createEditing(ctx) {
  const { state, dom } = ctx;
  const toast = (...args) => ctx.toast(...args);
  const decoder = new TextDecoder('utf-8', { fatal: false });

  let changesOpen = false;
  let author = loadAuthor();
  // The push token is held in memory only for the lifetime of the page; it is
  // never written to localStorage or the repo registry.
  let pushToken = '';

  /* ---------------------------------------------------------------- */
  /* Event wiring                                                      */
  /* ---------------------------------------------------------------- */

  function bindEvents() {
    dom.changesBtn.addEventListener('click', toggleChanges);
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
  }

  /** Show or hide every editing affordance based on the source's capabilities. */
  function applyEditableUI() {
    const editable = Boolean(state.source) && !state.source.readOnly;
    dom.changesBtn.hidden = !editable;
    dom.newFileBtn.hidden = !editable;
    dom.pushSection.hidden = !(editable && state.source.canPush);
  }

  /** Reset all editing state + UI (on repo open/close). */
  function reset() {
    state.editing = false;
    state.changedPaths = new Set();
    changesOpen = false;
    dom.changesPanel.hidden = true;
    dom.changesBtn.setAttribute('aria-pressed', 'false');
    closeNewFileModal();
    updateChangesBadge(0);
  }

  /** Global Escape fallback: close the new-file modal if it is open. */
  function onEscape() {
    if (!dom.newfileOverlay.hidden) closeNewFileModal();
  }

  /* ---------------------------------------------------------------- */
  /* Per-file Edit / Delete actions (live in the viewer header)        */
  /* ---------------------------------------------------------------- */

  /** Hide the per-file Edit/Delete actions (e.g. while loading or editing). */
  function hideViewerActions() {
    dom.viewerActions.hidden = true;
  }

  /**
   * Show Edit/Delete for editable sources. Editing is offered for text files;
   * deletion is offered for any file (images and binaries included).
   *
   * @param {'text'|'image'|'binary'} kind  how the viewer rendered the file
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
      ctx.showPlaceholder();
    } else {
      ctx.openFile(path);
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
    await ctx.openFile(path);
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
    ctx.showPlaceholder();
    hideViewerActions();
    await refreshChanges();
  }

  /** Reload the file list without resetting the user's expanded directories. */
  async function reloadFileListPreservingExpansion() {
    const files = await state.source.listFiles();
    state.files = files;
    state.fileSet = new Set(files);
    state.tree = buildFileTree(files);
    ctx.renderSidebar();
  }

  /* ---------------------------------------------------------------- */
  /* New-file modal                                                    */
  /* ---------------------------------------------------------------- */

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
    ctx.renderSidebar();
    dom.viewerHead.hidden = false;
    ctx.renderFilePath(path);
    renderEditor(path, '', { isNew: true });
  }

  /* ---------------------------------------------------------------- */
  /* Changes drawer: status, commit, push                             */
  /* ---------------------------------------------------------------- */

  function toggleChanges() {
    changesOpen = !changesOpen;
    if (changesOpen) ctx.closeHistory();
    dom.changesPanel.hidden = !changesOpen;
    dom.changesBtn.setAttribute('aria-pressed', String(changesOpen));
    if (changesOpen) loadChanges();
  }

  function closeChanges() {
    changesOpen = false;
    dom.changesPanel.hidden = true;
    dom.changesBtn.setAttribute('aria-pressed', 'false');
  }

  async function loadChanges() {
    if (!state.source) return;
    dom.changesBranch.textContent = state.source.getCurrentBranch();
    if (!dom.authorName.value) dom.authorName.value = author.name || '';
    if (!dom.authorEmail.value) dom.authorEmail.value = author.email || '';
    dom.pushSection.hidden = !state.source.canPush;
    await refreshChanges();
  }

  /**
   * Recompute working-tree status, update the badge and dirty markers, and
   * (when the drawer is open) re-render the change list. Safe to call after any
   * edit.
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
    if (!state.editing) ctx.renderSidebar();
    if (changesOpen) renderChangesList(changes);
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
        name.addEventListener('click', () => ctx.openFile(change.path));
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
    const nextAuthor = {
      name: dom.authorName.value.trim() || 'You',
      email: dom.authorEmail.value.trim() || 'you@example.com',
    };
    saveAuthor(nextAuthor);

    const btn = dom.commitBtn;
    const original = btn.textContent;
    btn.disabled = true;
    btn.textContent = 'Committing…';
    try {
      const { oid } = await state.source.commit({ message, author: nextAuthor });
      dom.commitMessage.value = '';
      toast(`Committed ${shortOid(oid)}`, 'success');

      // The file set is unchanged by a commit, so refresh head + history +
      // status in place rather than rebuilding (and collapsing) the tree.
      try {
        ctx.renderHead(await state.source.headCommit());
      } catch {
        /* leave the header as-is */
      }
      await ctx.reloadHistory();
      await refreshChanges();
      if (state.activePath && state.fileSet.has(state.activePath) && !state.editing) {
        ctx.openFile(state.activePath);
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
        token: pushToken,
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
      return parsed && typeof parsed === 'object' ? parsed : {};
    } catch {
      return {};
    }
  }

  function saveAuthor(next) {
    author = { name: next.name, email: next.email };
    try {
      localStorage.setItem(AUTHOR_KEY, JSON.stringify(author));
    } catch {
      /* storage may be unavailable; non-fatal */
    }
  }

  return {
    bindEvents,
    applyEditableUI,
    reset,
    onEscape,
    hideViewerActions,
    updateViewerActions,
    toggleChanges,
    closeChanges,
    refreshChanges,
  };
}
