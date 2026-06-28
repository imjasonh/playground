/**
 * Commit history side panel for the current branch.
 */
import { el } from './dom.js';
import { commitSummary, relativeTime, shortOid } from '../format.js';
import { refLabel } from '../repoSource.js';

/**
 * @param {{state: object, dom: Record<string, HTMLElement>}} ctx
 */
export function createHistory(ctx) {
  const { state, store, dom } = ctx;

  function toggle() {
    const open = !state.historyOpen;
    store.setState({ historyOpen: open, historyPath: null });
    dom.historyPanel.hidden = !open;
    dom.historyBtn.setAttribute('aria-pressed', String(open));
    if (open) load();
  }

  /** Open the panel scoped to a single file's commit history. */
  function showFile(path) {
    store.setState({ historyOpen: true, historyPath: path });
    dom.historyPanel.hidden = false;
    dom.historyBtn.setAttribute('aria-pressed', 'true');
    load();
  }

  /** Drop back from file history to the current ref's history. */
  function showBranch() {
    store.setState({ historyPath: null });
    load();
  }

  /** Close the panel (used when switching repositories). */
  function reset() {
    store.setState({ historyOpen: false, historyPath: null });
    dom.historyPanel.hidden = true;
    dom.historyBtn.setAttribute('aria-pressed', 'false');
  }

  function currentLabel() {
    const source = state.source;
    if (source && typeof source.getCurrentRef === 'function') return refLabel(source.getCurrentRef());
    return source ? source.getCurrentBranch() : '';
  }

  async function load() {
    if (!state.source) return;
    const path = state.historyPath;
    dom.historyBranch.textContent = path ? path : currentLabel();
    dom.commitList.replaceChildren(el('li', 'commit-item muted', 'Loading…'));
    try {
      const commits = path ? await loadFileLog(path) : await state.source.log(100);
      dom.commitList.replaceChildren();
      if (path) dom.commitList.appendChild(backRow());
      if (commits.length === 0) {
        dom.commitList.appendChild(
          el('li', 'commit-item muted', path ? 'No commits touched this file.' : 'No history.')
        );
        return;
      }
      for (const commit of commits) {
        dom.commitList.appendChild(commitRow(commit));
      }
    } catch (err) {
      dom.commitList.replaceChildren(el('li', 'commit-item muted', `History unavailable: ${err.message}`));
    }
  }

  function loadFileLog(path) {
    const source = state.source;
    if (typeof source.fileLog === 'function') return source.fileLog(path, 100);
    return source.log(100); // source without per-file history: show full log
  }

  /** A row that returns from file history to the current ref's history. */
  function backRow() {
    const li = el('li', 'commit-item history-back');
    const btn = el('button', 'commit-action', '\u2190 Back to history');
    btn.type = 'button';
    btn.addEventListener('click', showBranch);
    li.appendChild(btn);
    return li;
  }

  function commitRow(commit) {
    const item = el('li', 'commit-item');
    item.appendChild(el('p', 'commit-msg', commitSummary(commit.message)));
    const meta = el('div', 'commit-meta');
    meta.appendChild(el('span', 'commit-oid', shortOid(commit.oid)));
    if (commit.author.name) meta.appendChild(el('span', null, commit.author.name));
    if (commit.timestamp) meta.appendChild(el('span', null, relativeTime(commit.timestamp)));
    item.appendChild(meta);

    if (ctx.browseRef && commit.oid) {
      const actions = el('div', 'commit-actions');
      const browse = el('button', 'commit-action', 'Browse files');
      browse.type = 'button';
      browse.title = `Browse the tree at ${shortOid(commit.oid)}`;
      browse.addEventListener('click', () => ctx.browseRef({ type: 'commit', name: commit.oid }));
      actions.appendChild(browse);
      item.appendChild(actions);
    }
    return item;
  }

  return { toggle, showFile, showBranch, reset, load };
}
